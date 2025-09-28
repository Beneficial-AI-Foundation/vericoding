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
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): using get method to avoid bounds check issues */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            i <= x1.len(),
            result.len() == i,
            x1.len() == x2.len(),
        decreases x1.len() - i
    {
        let val1 = x1[i];
        let val2 = x2[i];
        result.push(val1 / val2);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}