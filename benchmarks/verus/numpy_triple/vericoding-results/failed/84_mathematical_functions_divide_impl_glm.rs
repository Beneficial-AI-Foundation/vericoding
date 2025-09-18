// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): fixed loop invariant syntax by grouping invariants in a block */
    let mut result = Vec::new();
    for i in 0..x1.len()
        invariant {
            0 <= i,
            i <= x1.len(),
            result.len() == i,
        }
    {
        result.push(x1[i] / x2[i]);
    }
    result
}
// </vc-code>

}
fn main() {}