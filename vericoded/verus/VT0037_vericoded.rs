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
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut result = arr;
    let mut i = 0;
    while i < values.len()
        invariant
            result.len() == arr.len() + i,
            forall|k: int| 0 <= k < arr.len() ==> result[k] == arr[k],
            forall|k: int| 0 <= k < i ==> result[arr.len() + k] == values[k],
            i <= values.len(),
        decreases values.len() - i
    {
        result.push(values[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}