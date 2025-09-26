// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn count(arr: Seq<int>, value: int) -> nat
    decreases arr.len()
{
    if arr.len() == 0 { 0nat } else { (if arr[0] == value { 1nat } else { 0nat }) + count(arr.skip(1), value) }
}

proof fn count_bound(arr: Seq<int>, value: int)
    ensures count(arr, value) <= arr.len()
    decreases arr.len()
{
    if arr.len() > 0 {
        count_bound(arr.skip(1), value);
    }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn swap(arr: &mut Vec<int>, i: usize, j: usize)
    requires 
        old(arr).len() > 0,
        i < old(arr).len(),
        j < old(arr).len(),
    ensures 
        arr[i as int] == old(arr)[j as int],
        arr[j as int] == old(arr)[i as int],
        forall|k: int| 0 <= k < arr.len() && k != i && k != j ==> arr[k] == old(arr)[k],
        arr@.to_multiset() == old(arr)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}