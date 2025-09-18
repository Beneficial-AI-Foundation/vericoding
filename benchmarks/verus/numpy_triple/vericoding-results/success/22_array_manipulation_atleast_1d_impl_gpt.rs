// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_vec_index_eq_from_eq<T>(v1: Vec<T>, v2: Vec<T>)
    requires
        v1 == v2,
    ensures
        forall|i: int| 0 <= i < v1.len() ==> v1[i] == v2[i],
{
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
    arr
}
// </vc-code>

}
fn main() {}