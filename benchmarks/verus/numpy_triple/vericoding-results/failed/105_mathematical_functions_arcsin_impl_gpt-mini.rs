// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): arcsin_map maps {-1,0,1} to {-2,0,2} */
fn arcsin_map(x: i8) -> i8
    requires
        -1 <= x as int && x as int <= 1,
    ensures
        (x as int == 0 ==> result as int == 0),
        (x as int == 1 ==> result as int == 2),
        (x as int == -1 ==> result as int == -2),
        -2 <= result as int && result as int <= 2,
{
    if x == 0 {
        0
    } else if x == 1 {
        2
    } else {
        -2
    }
}

/* helper modified by LLM (iteration 5): arcsin_map_monotone proves monotonicity of arcsin_map */
proof fn arcsin_map_monotone(a: i8, b: i8)
    requires
        -1 <= a as int && a as int <= 1,
        -1 <= b as int && b as int <= 1,
    ensures
        a as int <= b as int ==> arcsin_map(a) as int <= arcsin_map(b) as int,
{
    if a as int <= b as int {
        if a == b {
            assert(arcsin_map(a) == arcsin_map(b));
        } else if a == -1 {
            if b == 0 {
                assert(arcsin_map(a) == -2);
                assert(arcsin_map(b) == 0);
                assert(arcsin_map(a) <= arcsin_map(b));
            } else {
                assert(arcsin_map(a) == -2);
                assert(arcsin_map(b) == 2);
                assert(arcsin_map(a) <= arcsin_map(b));
            }
        } else {
            // a == 0 and b == 1
            assert(arcsin_map(a) == 0);
            assert(arcsin_map(b) == 2);
            assert(arcsin_map(a) <= arcsin_map(b));
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn numpy_arcsin(x: Vec<i8>) -> (result: Vec<i8>)
    requires 
        x@.len() > 0,
        forall|i: int| 0 <= i < x@.len() ==> -1 <= x[i] as int && x[i] as int <= 1,
    ensures
        result@.len() == x@.len(),
        forall|i: int| 0 <= i < result@.len() ==> {
            -2 <= result[i] as int && result[i] as int <= 2 &&
            (x[i] as int == 0 ==> result[i] as int == 0) &&
            (x[i] as int == 1 ==> result[i] as int == 2) &&
            (x[i] as int == -1 ==> result[i] as int == -2)
        },
        forall|i: int, j: int| 0 <= i < x@.len() && 0 <= j < x@.len() && x[i] as int <= x[j] as int ==> result[i] as int <= result[j] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct result vector using arcsin_map and return it */
    let n = x.len();
    let mut res = Vec::<i8>::new();
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i as int && i as int <= n as int,
            res@.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> res[k] as int == arcsin_map(x@[k]) as int,
        decreases n as int - i as int
    {
        let xv: i8 = x[i];
        let m: i8 = arcsin_map(xv);
        res.push(m);
        i = i + 1;
    }

    proof {
        let mut k: int = 0;
        while k < n as int
            invariant
                0 <= k && k <= n as int,
            decreases n as int - k
        {
            assert(res[k] as int == arcsin_map(x@[k]) as int);
            assert(-2 <= res[k] as int && res[k] as int <= 2);
            if x@[k] as int == 0 {
                assert(res[k] as int == 0);
            } else if x@[k] as int == 1 {
                assert(res[k] as int == 2);
            } else {
                assert(res[k] as int == -2);
            }
            k = k + 1;
        }

        let mut p: int = 0;
        while p < n as int
            invariant
                0 <= p && p <= n as int,
            decreases n as int - p
        {
            let mut q: int = 0;
            while q < n as int
                invariant
                    0 <= q && q <= n as int,
                decreases n as int - q
            {
                if x@[p] as int <= x@[q] as int {
                    arcsin_map_monotone(x@[p], x@[q]);
                    assert(arcsin_map(x@[p]) as int <= arcsin_map(x@[q]) as int);
                    assert(res[p] as int == arcsin_map(x@[p]) as int);
                    assert(res[q] as int == arcsin_map(x@[q]) as int);
                    assert(res[p] as int <= res[q] as int);
                }
                q = q + 1;
            }
            p = p + 1;
        }
    }

    let result = res;
    result
}

// </vc-code>

}
fn main() {}