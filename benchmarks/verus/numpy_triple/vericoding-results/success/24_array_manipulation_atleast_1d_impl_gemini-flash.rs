// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn atleast_1d_helper(arr: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result == arr,
        result.len() == arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> result[i] == arr[i],
{
    arr
}
// </vc-helpers>

// <vc-spec>
fn atleast_1d(arr: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result == arr,
        forall|i: int| 0 <= i < arr.len() ==> result[i] == arr[i],
// </vc-spec>
// <vc-code>
{
    let result = atleast_1d_helper(arr);
    result
}
// </vc-code>

}
fn main() {}