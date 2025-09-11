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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}