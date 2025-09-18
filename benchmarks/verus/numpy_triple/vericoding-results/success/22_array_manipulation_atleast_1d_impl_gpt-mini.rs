// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn vec_refl(arr: Vec<f64>) ensures arr == arr { }
// </vc-helpers>

// <vc-spec>
fn atleast_1d(arr: Vec<f64>) -> (result: Vec<f64>)
    ensures
        result == arr,
        forall|i: int| 0 <= i < arr.len() ==> result[i] == arr[i],
// </vc-spec>
// <vc-code>
{
    let result = arr;
    result
}
// </vc-code>

}
fn main() {}