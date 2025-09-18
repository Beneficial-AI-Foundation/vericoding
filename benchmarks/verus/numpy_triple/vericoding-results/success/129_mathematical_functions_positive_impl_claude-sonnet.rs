// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn positive(x: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == x[i],
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    for i in 0..x.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == x[j]
    {
        result.push(x[i]);
    }
    result
}
// </vc-code>

}
fn main() {}