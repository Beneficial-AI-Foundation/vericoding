// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn nditer(arr: Vec<i8>) -> (iter: (usize, Vec<i8>))
    ensures
        iter.0 == 0,
        iter.1@ == arr@,
        iter.0 <= arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> iter.1[i] == arr[i]
// </vc-spec>
// <vc-code>
{
    let iter = (0usize, arr);
    iter
}
// </vc-code>

}
fn main() {}