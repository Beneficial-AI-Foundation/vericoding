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

// <vc-helpers>
proof fn multiset_swap_preservation(v: Seq<int>, i: int, j: int, new_v: Seq<int>)
    requires
        0 <= i < v.len(),
        0 <= j < v.len(),
        new_v.len() == v.len(),
        new_v[i] == v[j],
        new_v[j] == v[i],
        forall|k: int| 0 <= k < v.len() && k != i && k != j ==> new_v[k] == v[k],
    ensures
        new_v.to_multiset() == v.to_multiset(),
{
    assert(new_v.to_multiset() == v.to_multiset()) by {
        reveal(Seq::to_multiset);
    }
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
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
{
    let temp = arr[i];
    arr.set(i, arr[j]);
    arr.set(j, temp);
    proof {
        multiset_swap_preservation(old(arr)@, i as int, j as int, arr@);
    }
}
// </vc-code>

fn main() {}

}