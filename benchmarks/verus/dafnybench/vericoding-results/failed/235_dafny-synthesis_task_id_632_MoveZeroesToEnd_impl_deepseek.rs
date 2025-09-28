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
proof fn count_append(arr1: Seq<i32>, arr2: Seq<i32>, value: i32)
    ensures count(arr1 + arr2, value) == count(arr1, value) + count(arr2, value),
    decreases arr1.len(),
{
    if arr1.len() == 0 {
    } else {
        count_append(arr1.skip(1), arr2, value);
    }
}

proof fn count_split(arr: Seq<i32>, idx: int)
    requires 0 <= idx <= arr.len(),
    ensures count(arr, 0) == count(arr.subrange(0, idx), 0) + count(arr.subrange(idx, arr.len() as int), 0),
{
    count_append(arr.subrange(0, idx), arr.subrange(idx, arr.len() as int), 0);
}

proof fn preserve_non_zero_order(arr: Seq<i32>, arr_new: Seq<i32>)
    requires
        arr.len() == arr_new.len(),
        arr_new.to_multiset() == arr.to_multiset(),
        forall|i: int, j: int| 0 <= i < j < arr_new.len() && arr_new[i] == 0 ==> arr_new[j] == 0,
    ensures forall|n: int, m: int| 0 <= n < m < arr.len() && arr[n] != 0 && arr[m] != 0 ==>
        exists|k: int, l: int| 0 <= k < l < arr_new.len() && arr_new[k] == arr[n] && arr_new[l] == arr[m],
{
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
    let old_arr = arr@;
    let mut i: usize = 0;
    let mut j: usize = arr.len() - 1;
    
    while i < j
        invariant
            0 <= i <= j < arr.len(),
            forall|k: int| 0 <= k < i as int ==> arr[k] != 0,
            forall|k: int| j as int < k < arr.len() as int ==> arr[k] == 0,
            arr@.to_multiset() == old_arr.to_multiset(),
            count(arr@, 0) == count(old_arr, 0),
        decreases j - i,
    {
        if arr[i] == 0 {
            proof {
                count_split(arr@, i as int);
                count_split(arr@, (i + 1) as int);
            }
            swap(arr, i, j);
            proof {
                assert(arr@.to_multiset() == old_arr.to_multiset());
                assert(count(arr@, 0) == count(old_arr, 0));
            }
            j = j - 1;
        } else {
            i = i + 1;
        }
    }
    
    proof {
        preserve_non_zero_order(old_arr, arr@);
    }
}
// </vc-code>

fn main() {}

}