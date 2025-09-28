// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): fixed spec! macro for predicate definition */
spec fn valid_iter(iter: (usize, Vec<i8>), original: Vec<i8>) -> bool {
    &&& iter.0 <= iter.1.len()
    &&& iter.1@ == original@
    &&& iter.1.len() == original.len()
}
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
    /* code modified by LLM (iteration 2): simple iterator initialization */
    let iter = (0, arr);
    iter
}
// </vc-code>

}
fn main() {}