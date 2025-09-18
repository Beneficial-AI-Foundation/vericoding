// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn id_vec<T>(v: Vec<T>) -> (res: Vec<T>) ensures res@ == v@ { v }
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
    let v = arr;
    let idx: usize = 0;
    (idx, v)
}
// </vc-code>

}
fn main() {}