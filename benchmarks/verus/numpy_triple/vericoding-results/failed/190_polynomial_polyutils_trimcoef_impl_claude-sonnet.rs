// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove spec operations that don't exist for f32 */
fn abs_f32(x: f32) -> (result: f32) {
    if x >= 0.0f32 {
        x
    } else {
        0.0f32 - x
    }
}
// </vc-helpers>

// <vc-spec>
fn trimcoef(c: Vec<f32>, tol: f32) -> (result: Vec<f32>)
    ensures
        result.len() >= 1,
        result.len() <= c.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use custom abs_f32 without spec functions */
    if c.len() == 0 {
        return vec![0.0f32];
    }
    
    let mut end_idx = c.len();
    
    while end_idx > 1
        invariant
            end_idx >= 1,
            end_idx <= c.len(),
    {
        if abs_f32(c[end_idx - 1]) > tol {
            break;
        }
        end_idx = end_idx - 1;
    }
    
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < end_idx
        invariant
            i <= end_idx,
            end_idx >= 1,
            end_idx <= c.len(),
            result.len() == i,
    {
        result.push(c[i]);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}