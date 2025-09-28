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
    /* code modified by LLM (iteration 2): [changed loop invariants to use forall quantifiers instead of subrange equality] */
    let ghost arr_view = arr.view();
    let mut result = arr;
    let mut i: usize = 0;
    while i < values.len()
        invariant
            0 <= i <= values.len(),
            result.len() == arr_view.len() + i,
            forall|k: int| 0 <= k < arr_view.len() ==> result[k] == arr_view[k],
            forall|k: int| 0 <= k < i ==> result[arr_view.len() + k] == values[k],
        decreases values.len() - i
    {
        result.push(values[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}