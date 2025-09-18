// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn seq_of_vec(v: Vec<f32>) -> Seq<f32> { v@ }

proof fn vec_seq_len(v: Vec<f32>) ensures v.len() == seq_of_vec(v).len() { }
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