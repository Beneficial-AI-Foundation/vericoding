// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn swap(arr: &mut Vec<i32>, i: usize, j: usize)
    requires 
        i < old(arr).len(),
        j < old(arr).len(),
    ensures
        arr[i as int] == old(arr)[j as int],
        arr[j as int] == old(arr)[i as int],
        forall|k: int| 0 <= k < arr.len() && k != i && k != j ==> arr[k] == old(arr)[k],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}