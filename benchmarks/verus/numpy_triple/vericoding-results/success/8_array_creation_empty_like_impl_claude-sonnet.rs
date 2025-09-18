// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_empty_like(prototype: &Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == prototype.len(),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] == 0.0f32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let len = prototype.len();
    let mut result = Vec::new();
    let mut i = 0;
    while i < len
        invariant
            result.len() == i,
            i <= len,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == 0.0f32,
        decreases len - i,
    {
        result.push(0.0f32);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}