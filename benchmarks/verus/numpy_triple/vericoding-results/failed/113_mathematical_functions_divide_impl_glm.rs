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
    /* code modified by LLM (iteration 2): fixed loop invariant to ensure vector bounds */
    let mut result = Vec::new();
    let mut i = 0;
    let n = x1.len();
    while i < n
        invariant
            i <= n,
            result.len() == i,
            n == x1.len(),
            n == x2.len(),
        decreases n - i,
    {
        result.push(x1[i] / x2[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}