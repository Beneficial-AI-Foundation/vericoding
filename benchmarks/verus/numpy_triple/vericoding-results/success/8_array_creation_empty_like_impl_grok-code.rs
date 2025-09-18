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
    let len = prototype.len();
    let mut index = 0;
    let mut result = Vec::new();
    while index < len
        invariant
            result.len() == index,
            forall|j: int| 0 <= j < index ==> result[j] == 0.0f32,
            0 <= index <= len
        decreases len - index
    {
        result.push(0.0f32);
        index += 1;
    }
    result
}
// </vc-code>

}
fn main() {}