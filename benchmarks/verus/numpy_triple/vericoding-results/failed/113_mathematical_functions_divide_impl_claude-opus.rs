// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added helper predicate to check all elements are non-zero */
spec fn all_nonzero(v: Vec<f32>) -> bool {
    forall|i: int| 0 <= i < v.len() ==> v@[i] != 0.0
}
// </vc-helpers>

// <vc-spec>
fn numpy_divide(x1: Vec<f32>, x2: Vec<f32>) -> (result: Vec<f32>)
    requires 
        x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed indexing - removed 'as usize' since i is already usize */
    assert(all_nonzero(x2));
    let mut result = Vec::new();
    let n = x1.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            n == x1.len(),
            n == x2.len(),
        decreases n - i
    {
        assert(x2[i] != 0.0);
        let quotient = x1[i] / x2[i];
        result.push(quotient);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}