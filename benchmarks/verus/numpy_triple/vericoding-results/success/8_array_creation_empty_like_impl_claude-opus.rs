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
    let mut result = Vec::new();
    let mut i = 0;
    while i < prototype.len()
        invariant
            i <= prototype.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == 0.0f32,
        decreases prototype.len() - i
    {
        result.push(0.0f32);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}