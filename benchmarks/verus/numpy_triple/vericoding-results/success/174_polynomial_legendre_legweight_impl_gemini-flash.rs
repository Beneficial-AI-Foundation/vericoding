// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Removed unnecessary specification function as it's not directly used for proving the code. */
// </vc-helpers>

// <vc-spec>
fn legweight(x: Vec<f32>) -> (result: Vec<f32>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == 1.0f32
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Added decreases clause to loop. */
{
    let mut result: Vec<f32> = Vec::new();
    let x_len = x.len();
    while result.len() < x_len
        invariant
            x_len == x.len(),
            result.len() <= x_len,
            forall|i: int| 0 <= i < result.len() ==> result[i] == 1.0f32
        decreases x_len - result.len()
    {
        result.push(1.0f32);
    }
    result
}
// </vc-code>

}
fn main() {}