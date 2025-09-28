// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): multiply two i8s using i16 intermediate; avoid exec 'int' usage and prove relation in proof blocks */
fn mul_i8(x: i8, y: i8) -> (res: i8)
    requires
        -128 <= (x as int) * (y as int),
        (x as int) * (y as int) <= 127,
    ensures
        res as int == x as int * y as int,
{
    let x16: i16 = x as i16;
    let y16: i16 = y as i16;
    proof {
        assert(-32768 <= (x as int));
        assert((x as int) <= 127);
        assert(-32768 <= (y as int));
        assert((y as int) <= 127);
        assert(-32768 <= (x as int) * (y as int) && (x as int) * (y as int) <= 32767);
    }
    let p16: i16 = x16 * y16;
    proof {
        assert(p16 as int == (x as int) * (y as int));
    }
    let r: i8 = p16 as i8;
    proof {
        assert(r as int == p16 as int);
        assert(r as int == (x as int) * (y as int));
    }
    r
}
// </vc-helpers>

// <vc-spec>
fn multiply(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] as int == a[i] as int * b[i] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): element-wise multiply with loop invariants; use helper for safe i8 product */
    let n = a.len();
    let mut result: Vec<i8> = Vec::new();
    result.reserve(n);
    let mut i: usize = 0;
    while i < n
        invariant
            a.len() == b.len(),
            n == a.len(),
            n == b.len(),
            i <= n,
            result.len() == i,
            forall|k: int| 0 <= k < i as int ==> result[k] as int == a[k] as int * b[k] as int,
        decreases n - i
    {
        proof {
            assert(i < n);
            assert(i < a.len());
            assert(i < b.len());
        }
        let ai = a[i];
        let bi = b[i];
        let prod = mul_i8(ai, bi);
        result.push(prod);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}