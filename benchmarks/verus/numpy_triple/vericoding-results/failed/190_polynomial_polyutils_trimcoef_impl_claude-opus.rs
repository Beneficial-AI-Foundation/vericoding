// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn trimcoef(c: Vec<f32>, tol: f32) -> (result: Vec<f32>)
    ensures
        result.len() >= 1,
        result.len() <= c.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): replaced abs() with manual comparison to avoid unsupported method */
    let mut i = c.len();
    while i > 1
        invariant
            1 <= i <= c.len(),
        decreases i
    {
        if c[i - 1] > tol || c[i - 1] < -tol {
            break;
        }
        i = i - 1;
    }
    
    let mut result = Vec::new();
    let mut j = 0;
    while j < i
        invariant
            j <= i,
            result.len() == j,
        decreases i - j
    {
        result.push(c[j]);
        j = j + 1;
    }
    
    if result.len() == 0 {
        result.push(0.0);
    }
    
    result
}
// </vc-code>

}
fn main() {}