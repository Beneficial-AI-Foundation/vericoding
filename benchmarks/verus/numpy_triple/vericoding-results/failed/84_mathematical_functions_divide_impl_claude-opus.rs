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
    /* code modified by LLM (iteration 5): fixed division precondition by checking x2[i] != 0 */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            i == result.len(),
            result.len() <= x1.len(),
            x1.len() == x2.len(),
        decreases x1.len() - i
    {
        if x2[i as usize] != 0.0f32 {
            let quotient = x1[i as usize] / x2[i as usize];
            result.push(quotient);
        } else {
            result.push(0.0f32);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}