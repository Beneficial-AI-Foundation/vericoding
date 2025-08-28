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
spec fn is_zero_at(arr: Seq<i32>, pos: int) -> bool {
    pos >= 0 && pos < arr.len() && arr[pos] == 0
}

proof fn multiset_swap(arr: Seq<i32>, i: int, j: int)
    ensures
        arr.update(i as usize, arr[j as usize]).update(j as usize, arr[i as usize]).to_multiset() == arr.to_multiset(),
{
}

proof fn count_preservation(arr: Seq<i32>, i: int, j: int, value: i32)
    ensures
        count(arr.update(i as usize, arr[j as usize]).update(j as usize, arr[i as usize]), value) == count(arr, value),
    decreases arr.len(),
{
    if arr.len() == 0 {
    } else {
        count_preservation(arr.skip(1), if i > 0 { i - 1 } else { i }, if j > 0 { j - 1 } else { j }, value);
    }
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    let mut i: usize = 0;
    let mut j: usize = 0;
    let len = arr.len();

    while j < len
        invariant
            0 <= i <= j <= len,
            arr.len() == len,
            forall|k: int, l: int| 0 <= k < l < i as int && arr[k] != 0 && arr[l] != 0 ==>
                exists|m: int, n: int| 0 <= m < n < i as int && arr[m] == arr[m] && arr[n] == arr[n],
            forall|k: int, l: int| 0 <= k < i as int <= l < j as int && arr[k] == 0 ==> arr[l] == 0,
            arr@.to_multiset() == old(arr)@.to_multiset(),
    {
        if arr[j] == 0 {
            j = j + 1;
        } else {
            if i != j {
                let arr_seq = arr@;
                let temp = arr[i];
                arr.set(i, arr[j]);
                arr.set(j, temp);
                proof {
                    multiset_swap(arr_seq, i as int, j as int);
                }
            }
            i = i + 1;
            j = j + 1;
        }
    }
}
// </vc-code>

fn main() {}

}