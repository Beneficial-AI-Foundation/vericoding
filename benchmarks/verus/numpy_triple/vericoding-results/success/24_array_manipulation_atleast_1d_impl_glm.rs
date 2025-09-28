// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn atleast_1d(arr: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result == arr,
        forall|i: int| 0 <= i < arr.len() ==> result[i] == arr[i],
// </vc-spec>
// <vc-code>
{
    arr
}
// </vc-code>

}
fn main() {}