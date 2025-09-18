// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed floating-point comparison using f32::spec_ge */
fn abs_f32(x: f32) -> (result: f32)
    ensures f32::spec_ge(result, 0.0)
{
    if x < 0.0 {
        -x
    } else {
        x
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
/* code modified by LLM (iteration 5): No changes needed */
{
    if c.len() == 0 {
        vec![0.0]
    } else {
        let mut end_index = c.len();
        let mut i = c.len();
        while i > 0
            invariant 0 <= i <= c.len()
        {
            if abs_f32(c[i-1]) <= tol {
                i = i - 1;
            } else {
                break;
            }
        }
        end_index = i;

        if end_index == 0 {
            vec![0.0]
        } else {
            let mut result = Vec::new();
            for j in 0..end_index {
                result.push(c[j]);
            }
            result
        }
    }
}
// </vc-code>

}
fn main() {}