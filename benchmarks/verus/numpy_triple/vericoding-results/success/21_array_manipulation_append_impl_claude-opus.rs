// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_append(arr: Vec<f32>, values: Vec<f32>) -> (result: Vec<f32>)
    ensures
        result.len() == arr.len() + values.len(),
        forall|i: int| 0 <= i < arr.len() ==> result[i] == arr[i],
        forall|j: int| 0 <= j < values.len() ==> result[arr.len() + j] == values[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clauses to loops */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result[k] == arr[k],
        decreases arr.len() - i,
    {
        result.push(arr[i]);
        i = i + 1;
    }
    let mut j: usize = 0;
    while j < values.len()
        invariant
            j <= values.len(),
            result.len() == arr.len() + j,
            forall|k: int| 0 <= k < arr.len() ==> result[k] == arr[k],
            forall|k: int| 0 <= k < j ==> result[arr.len() + k] == values[k],
        decreases values.len() - j,
    {
        result.push(values[j]);
        j = j + 1;
    }
    result
}
// </vc-code>

}
fn main() {}