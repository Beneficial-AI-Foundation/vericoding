// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): The problem is related to the missing `decreases` clause. An empty `<vc-helpers>` section is provided here as it doesn't need external helper functions. */

// </vc-helpers>

// <vc-spec>
fn numpy_empty_like(prototype: &Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == prototype.len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] == 0.0f32,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Added decreases clause to the `while` loop to fix the verification error. */
{
    let prototype_len = prototype.len();
    let mut result: Vec<f32> = Vec::new();
    let mut i = 0;
    while i < prototype_len
        invariant
            0 <= i <= prototype_len,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == 0.0f32,
        decreases prototype_len - i,
    {
        result.push(0.0f32);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}