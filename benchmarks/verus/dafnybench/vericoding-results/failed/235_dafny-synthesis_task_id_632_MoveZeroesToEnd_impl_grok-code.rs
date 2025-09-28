use vstd::prelude::*;

verus! {

fn swap(arr: &mut Vec<i32>, i: usize, j: usize)
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
    assume(false);
}

spec fn count(arr: Seq<i32>, value: i32) -> nat
    decreases arr.len(),
{
    if arr.len() == 0 {
        0nat
    } else {
        (if arr[0] == value { 1nat } else { 0nat }) + count(arr.skip(1), value)
    }
}

proof fn count_bound(arr: Seq<i32>, value: i32)
    ensures count(arr, value) <= arr.len(),
    decreases arr.len(),
{
    if arr.len() == 0 {
    } else {
        count_bound(arr.skip(1), value);
    }
}

// <vc-helpers>
spec fn non_zeros(s: Seq<i32>) -> Seq<i32>
    decreases s.len(),
{
    if s.len() == 0 {
        seq![]
    } else {
        if s[0] != 0 {
            seq![s[0]] + non_zeros(s.skip(1))
        } else {
            non_zeros(s.skip(1))
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn move_zeros_to_end(arr: &mut Vec<i32>)
    requires old(arr).len() >= 2,
    ensures
        // Same size
        arr.len() == old(arr).len(),
        // Zeros to the right of the first zero
        forall|i: int, j: int| 0 <= i < j < arr.len() && arr[i] == 0 ==> arr[j] == 0,
        // The final array is a permutation of the original one
        arr@.to_multiset() == old(arr)@.to_multiset(),
        // Relative order of non-zero elements is preserved
        forall|n: int, m: int| 0 <= n < m < arr.len() && old(arr)[n] != 0 && old(arr)[m] != 0 ==>
            exists|k: int, l: int| 0 <= k < l < arr.len() && arr[k] == old(arr)[n] && arr[l] == old(arr)[m],
        // Number of zeros is preserved
// </vc-spec>
// <vc-code>
{
    let old_arr: Ghost<Seq<i32>> = Ghost(arr@);
    let mut pos = 0;
    let mut idx = 0;
    while idx < arr.len()
        invariant
            0 <= pos <= idx <= arr.len(),
            non_zeros(arr@.subrange(0, pos as int)) == non_zeros(old_arr.0.subrange(0, idx as int)),
            forall|i: int| 0 <= i < pos ==> arr@[i] != 0,
            forall|i: int| pos <= i < idx ==> arr@[i] == 0,
            forall|j: int| idx <= j < arr@.len() ==> arr@[j] == old_arr.0@[j],
            arr@.to_multiset() == old_arr.0.to_multiset(),
    {
        if arr[idx] != 0 {
            let temp = arr[pos];
            arr[pos] = arr[idx];
            arr[idx] = temp;
            pos += 1;
        }
        idx += 1;
    }
}
// </vc-code>

fn main() {}

}