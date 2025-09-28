// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): inverted if condition to guide the verifier */
fn safe_div(x: f32, y: f32) -> (z: f32)
{
    if y == 0.0 {
        0.0
    } else {
        x / y
    }
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
    /* code modified by LLM (iteration 5): no functional change, fix is in helper */
    let mut result: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            i <= x1.len(),
            result.len() == i,
        decreases x1.len() - i
    {
        let val1 = x1[i];
        let val2 = x2[i];
        result.push(safe_div(val1, val2));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}