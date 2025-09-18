// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_full_like(a: Vec<f32>, fill_value: f32) -> (result: Vec<f32>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == fill_value,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to the while loop to ensure termination */
    let mut result: Vec<f32> = Vec::new();
    while result.len() < a.len()
        invariant
            0 <= result.len() <= a.len(),
            forall |i: int| 0 <= i < result.len() ==> result[i] == fill_value,
        decreases a.len() - result.len()
    {
        result.push(fill_value);
    }
    result
}
// </vc-code>

}
fn main() {}