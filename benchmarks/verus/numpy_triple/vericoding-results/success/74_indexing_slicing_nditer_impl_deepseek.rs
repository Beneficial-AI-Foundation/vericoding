// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn nditer_proof(arr: Vec<f32>) -> (iter: (usize, Vec<f32>))
    ensures
        iter.0 == 0,
        iter.1@ == arr@,
        iter.0 <= arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> iter.1[i] == arr[i]
{
    (0, arr)
}
// </vc-helpers>

// <vc-spec>
fn nditer(arr: Vec<f32>) -> (iter: (usize, Vec<f32>))
    ensures
        iter.0 == 0,
        iter.1@ == arr@,
        iter.0 <= arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> iter.1[i] == arr[i]
// </vc-spec>
// <vc-code>
{
    (0, arr)
}
// </vc-code>

}
fn main() {}