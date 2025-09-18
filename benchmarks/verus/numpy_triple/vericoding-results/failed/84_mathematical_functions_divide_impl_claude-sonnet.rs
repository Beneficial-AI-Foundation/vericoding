// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added helper to check non-zero precondition */
spec fn all_non_zero(v: Vec<f32>) -> bool {
    forall|i: int| 0 <= i < v.len() ==> v@[i] != 0.0f32
}
// </vc-helpers>

// <vc-spec>
fn numpy_divide(x1: Vec<f32>, x2: Vec<f32>) -> (result: Vec<f32>)
    requires 
        x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < x1.len() ==> x2[i] != 0.0f32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed invalid assertion that depends on postcondition */
    let mut result: Vec<f32> = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            result.len() == i,
            x1.len() == x2.len()
        decreases x1.len() - i
    {
        assert(i < x1.len());
        assert(i < x2.len());
        result.push(x1[i] / x2[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}