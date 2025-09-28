// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn chebweight(x: Vec<f32>) -> (result: Vec<f32>)
    requires 
        x.len() > 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): replaced iterator with loop to avoid unsupported collect */
    let n = x.len();
    let mut result = Vec::with_capacity(n);
    for j in 0..n {
        if j == 0 || j == n - 1 {
            if j % 2 == 0 {
                result.push(0.5);
            } else {
                result.push(-0.5);
            }
        } else {
            if j % 2 == 0 {
                result.push(1.0);
            } else {
                result.push(-1.0);
            }
        }
    }
    result
}
// </vc-code>

}
fn main() {}