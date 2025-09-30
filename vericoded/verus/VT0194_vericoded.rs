// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn take(arr: Vec<f32>, indices: Vec<usize>) -> (result: Vec<f32>)
    requires
        forall|i: int| 0 <= i < indices@.len() ==> indices[i] < arr@.len(),
    ensures
        result@.len() == indices@.len(),
        forall|i: int| 0 <= i < indices@.len() ==> result[i] == arr[indices[i] as int],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to while loop */
    let mut result = Vec::new();
    let mut i = 0;
    while i < indices.len()
        invariant
            0 <= i <= indices.len(),
            result@.len() == i as int,
            forall|j: int| 0 <= j < i ==> result[j] == arr[indices[j] as int],
            forall|j: int| 0 <= j < indices@.len() ==> indices[j] < arr@.len(),
        decreases indices.len() - i
    {
        let index = indices[i];
        let value = arr[index];
        result.push(value);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}