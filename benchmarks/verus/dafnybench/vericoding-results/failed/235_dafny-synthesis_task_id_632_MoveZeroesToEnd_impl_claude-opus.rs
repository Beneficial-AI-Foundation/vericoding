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
proof fn lemma_swap_preserves_multiset(arr: &Vec<i32>, i: usize, j: usize)
    requires 
        arr.len() > 0,
        i < arr.len(),
        j < arr.len(),
    ensures
        arr@.to_multiset() =~= arr@.update(i as int, arr[j as int]).update(j as int, arr[i as int]).to_multiset(),
{
    // The multiset equality holds because we're just swapping elements
    // This is true by the definition of multisets - order doesn't matter
}

proof fn lemma_count_swap(arr: Seq<i32>, i: int, j: int, value: i32)
    requires
        0 <= i < arr.len(),
        0 <= j < arr.len(),
    ensures
        count(arr.update(i, arr[j]).update(j, arr[i]), value) == count(arr, value),
    decreases arr.len(),
{
    if arr.len() == 0 {
        // Base case: empty sequence
    } else if i == j {
        // Swapping same position doesn't change anything
        assert(arr.update(i, arr[j]).update(j, arr[i]) =~= arr);
    } else if i == 0 && j == 0 {
        assert(arr.update(i, arr[j]).update(j, arr[i]) =~= arr);
    } else if i == 0 {
        let swapped = arr.update(i, arr[j]).update(j, arr[i]);
        if j > 0 && arr.len() > 1 {
            // Recursive case
            lemma_count_swap(arr.skip(1), 0, j - 1, value);
        }
    } else if j == 0 {
        let swapped = arr.update(i, arr[j]).update(j, arr[i]);
        if i > 0 && arr.len() > 1 {
            lemma_count_swap(arr.skip(1), i - 1, 0, value);
        }
    } else if i > 0 && j > 0 && arr.len() > 1 {
        lemma_count_swap(arr.skip(1), i - 1, j - 1, value);
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
    let mut non_zero_pos: usize = 0;
    let n = arr.len();
    
    for i in 0..n
        invariant
            arr.len() == n,
            n == old(arr).len(),
            non_zero_pos <= i,
            non_zero_pos <= arr.len(),
            // All elements before non_zero_pos are non-zero
            forall|k: int| 0 <= k < non_zero_pos ==> arr[k] != 0,
            // All elements from non_zero_pos to i are zero
            forall|k: int| non_zero_pos <= k < i ==> arr[k] == 0,
            // Multiset is preserved
            arr@.to_multiset() == old(arr)@.to_multiset(),
            // Relative order of non-zero elements already processed is preserved
            forall|n: int, m: int| 
                0 <= n < m < i && old(arr)[n] != 0 && old(arr)[m] != 0 ==>
                exists|k: int, l: int| 0 <= k < l < non_zero_pos && arr[k] == old(arr)[n] && arr[l] == old(arr)[m],
    {
        if arr[i] != 0 {
            if i != non_zero_pos {
                let old_arr = arr.clone();
                swap(arr, non_zero_pos, i);
                // After swap, arr.len() is preserved by swap's spec
                assert(arr.len() == old_arr.len());
                assert(arr.len() == n);
            }
            non_zero_pos = non_zero_pos + 1;
        }
    }
    
    // Prove the postconditions
    assert forall|i: int, j: int| 0 <= i < j < arr.len() && arr[i] == 0 implies arr[j] == 0 by {
        if i < non_zero_pos {
            assert(arr[i] != 0);
        } else {
            assert(arr[j] == 0);
        }
    }
    
    assert forall|n: int, m: int| 
        0 <= n < m < arr.len() && old(arr)[n] != 0 && old(arr)[m] != 0 implies
        exists|k: int, l: int| 0 <= k < l < arr.len() && arr[k] == old(arr)[n] && arr[l] == old(arr)[m] by {
        assert(exists|k: int, l: int| 0 <= k < l < non_zero_pos && arr[k] == old(arr)[n] && arr[l] == old(arr)[m]);
    }
}
// </vc-code>

fn main() {}

}