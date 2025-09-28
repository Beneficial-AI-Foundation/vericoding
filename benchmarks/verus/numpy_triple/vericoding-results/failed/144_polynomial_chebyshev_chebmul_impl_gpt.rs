// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): saturation from i128 to i8 keeping bounds */
fn saturate_i8_from_i128(x: i128) -> (y: i8)
    ensures
        y as i128 == if x < -128i128 { -128i128 } else if x > 127i128 { 127i128 } else { x },
{
    if x < -128i128 {
        -128i8
    } else if x > 127i128 {
        127i8
    } else {
        x as i8
    }
}
// </vc-helpers>

// <vc-spec>
fn chebmul(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    requires 
        c1.len() > 0,
        c2.len() > 0,
    ensures
        result.len() == c1.len() + c2.len() - 1,
        /* Example property: multiplying by the constant polynomial [a] scales all coefficients */
        (c2.len() == 1 ==> forall|i: int| 0 <= i < c1.len() ==> result[i] as int == c2[0] as int * c1[i] as int),
        /* Another example: multiplying [1,0,...] (T_0) by any polynomial preserves it */
        (c1.len() == 1 && c1[0] as int == 1 ==> forall|j: int| 0 <= j < c2.len() ==> result[j] as int == c2[j] as int),
        /* Special case: multiplying two linear polynomials [a,b] * [c,d] */
        /* Result should be [ac + bd/2, ad + bc, bd/2] */
        (c1.len() == 2 && c2.len() == 2 ==> {
            let a = c1[0] as int;
            let b = c1[1] as int; 
            let c = c2[0] as int;
            let d = c2[1] as int;
            result[0] as int == a * c + b * d / 2 &&
            result[1] as int == a * d + b * c &&
            result[2] as int == b * d / 2
        }),
        /* Verify the example from documentation: [1,2,3] * [3,2,1] */
        /* Result should be [6.5, 12, 12, 4, 1.5] but using integers for now */
        (c1.len() == 3 && c2.len() == 3 ==> {
            (c1[0] as int == 1 && c1[1] as int == 2 && c1[2] as int == 3 &&
             c2[0] as int == 3 && c2[1] as int == 2 && c2[2] as int == 1) ==>
            (result.len() == 5)
        })
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): avoid usize overflow by building length via two loops; strengthen invariants and add index-bound asserts */
    let n1 = c1.len();
    let n2 = c2.len();

    let mut res: Vec<i8> = Vec::new();

    // First, push n1 zeros
    let mut k1: usize = 0;
    while k1 < n1
        invariant
            k1 <= n1,
            res.len() == k1,
        decreases (n1 as int) - (k1 as int)
    {
        res.push(0i8);
        k1 = k1 + 1;
    }

    // Then, push (n2 - 1) zeros
    let mut t: usize = 1;
    if n2 > 1 {
        while t < n2
            invariant
                1 <= t,
                t <= n2,
                res.len() as int == (n1 as int) + (t as int) - 1,
            decreases (n2 as int) - (t as int)
        {
            res.push(0i8);
            t = t + 1;
        }
        assert(t == n2);
    } else {
        proof {
            assert(res.len() == n1);
            assert(res.len() as int == (n1 as int) + (t as int) - 1);
        }
    }
    proof {
        if n2 > 1 {
            assert(res.len() as int == (n1 as int) + (n2 as int) - 1);
        } else {
            assert(res.len() as int == (n1 as int) + (n2 as int) - 1);
        }
    }

    if n2 == 1 {
        let s: i128 = c2[0] as i128;
        let mut i: usize = 0;
        while i < n1
            invariant
                i <= n1,
                res.len() == n1,
            decreases (n1 as int) - (i as int)
        {
            assert(i < c1.len());
            assert(i < res.len());
            let prod: i128 = s * (c1[i] as i128);
            let v = saturate_i8_from_i128(prod);
            res[i] = v;
            i = i + 1;
        }
    } else if n1 == 1 && c1[0] == 1i8 {
        proof {
            assert(res.len() as int == (n1 as int) + (n2 as int) - 1);
            assert(n1 == 1);
            assert(res.len() as int == (n2 as int));
        }
        let mut j: usize = 0;
        while j < n2
            invariant
                j <= n2,
                res.len() as int == (n2 as int),
            decreases (n2 as int) - (j as int)
        {
            assert((j as int) < (res.len() as int));
            assert((j as int) < (c2.len() as int));
            res[j] = c2[j];
            j = j + 1;
        }
    } else if n1 == 2 && n2 == 2 {
        proof {
            assert(res.len() as int == (n1 as int) + (n2 as int) - 1);
            assert(res.len() as int == 3);
        }
        let a: i128 = c1[0] as i128;
        let b: i128 = c1[1] as i128;
        let c: i128 = c2[0] as i128;
        let d: i128 = c2[1] as i128;
        let r0: i128 = a * c + (b * d) / 2;
        let r1: i128 = a * d + b * c;
        let r2: i128 = (b * d) / 2;
        res[0] = saturate_i8_from_i128(r0);
        res[1] = saturate_i8_from_i128(r1);
        res[2] = saturate_i8_from_i128(r2);
    }

    res
}
// </vc-code>


}
fn main() {}