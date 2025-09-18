// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn take(arr: Vec<f32>, indices: Vec<usize>) -> (result: Vec<f32>)
    requires
        forall|i: int| 0 <= i < indices.len() ==> indices[i] < arr.len(),
    ensures
        result.len() == indices.len(),
        forall|i: int| 0 <= i < indices.len() ==> result[i] == arr[indices[i] as int],
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    for i in 0..indices.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == arr[indices[j] as int],
            forall|k: int| 0 <= k < indices.len() ==> indices[k] < arr.len(),
    {
        let index = indices[i];
        let value = arr[index];
        result.push(value);
    }
    result
}
// </vc-code>

}
fn main() {}