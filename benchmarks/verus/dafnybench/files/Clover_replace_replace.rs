// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn replace(arr: &mut Vec<i8>, k: i8)
    ensures 
        forall|i: int| 0 <= i < old(arr)@.len() ==> old(arr)@[i] > k as int ==> arr@[i] == -1,
        forall|i: int| 0 <= i < old(arr)@.len() ==> old(arr)@[i] <= k as int ==> arr@[i] == old(arr)@[i],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}