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
    /* code modified by LLM (iteration 4): Added decreases clause to while loop */
    let n = x.len();
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j && j < i ==> result@[j] == if j == 0 || j == n - 1 { 0.5f32 } else { 1.0f32 },
        decreases n - i
    {
        if i == 0 || i == n - 1 {
            result.push(0.5f32);
        } else {
            result.push(1.0f32);
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}