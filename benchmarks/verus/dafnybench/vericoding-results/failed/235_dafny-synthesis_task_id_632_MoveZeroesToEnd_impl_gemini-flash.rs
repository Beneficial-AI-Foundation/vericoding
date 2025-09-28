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
spec fn count_zeros_in_range(s: Seq<i32>, start: int, end: int) -> nat
    decreases (end - start) as nat
{
    if start >= end {
        0nat
    } else {
        (if s[start] == 0 { 1nat } else { 0nat }) + count_zeros_in_range(s, start + 1, end)
    }
}

proof fn count_zeros_in_range_split(s: Seq<i32>, start: int, mid: int, end: int)
    requires 0 <= start <= mid <= end <= s.len()
    ensures
        count_zeros_in_range(s, start, end) ==
        count_zeros_in_range(s, start, mid) + count_zeros_in_range(s, mid, end)
    decreases (end - start) as nat
{
    if start >= end {
    } else if start == mid {
        assert(count_zeros_in_range(s, start, end) == count_zeros_in_range(s, mid, end));
    } else {
        count_zeros_in_range_split(s, start + 1, mid, end);
    }
}

proof fn count_zeros_in_range_le_len(s: Seq<i32>, start: int, end: int)
    requires 0 <= start <= end <= s.len()
    ensures count_zeros_in_range(s, start, end) <= (end - start) as nat
    decreases (end - start) as nat
{
    if start >= end {
    } else {
        count_zeros_in_range_le_len(s, start + 1, end);
    }
}

proof fn swap_properties(old_arr: Seq<i32>, i: usize, j: usize, new_arr: Seq<i32>)
    requires
        old_arr.len() > 0,
        i < old_arr.len(),
        j < old_arr.len(),
        new_arr.len() == old_arr.len(),
        new_arr.index(i as int) == old_arr.index(j as int),
        new_arr.index(j as int) == old_arr.index(i as int),
        forall |k: int| 0 <= k < old_arr.len() && k != i as int && k != j as int ==> new_arr.index(k) == old_arr.index(k),
    ensures
        new_arr.to_multiset() == old_arr.to_multiset()
{
    let multiset_i = multiset![old_arr[i as int]];
    let multiset_j = multiset![old_arr[j as int]];

    assert(new_arr.to_multiset() =~~= old_arr.to_multiset()
        .subtract(multiset_i).subtract(multiset_j)
        .add(multiset![new_arr[i as int]]).add(multiset![new_arr[j as int]]));
}


fn swap_elem(arr: &mut Vec<i32>, i: usize, j: usize)
    requires
        arr.len() > 0,
        i < arr.len(),
        j < arr.len(),
    ensures
        arr[i as int] == old(arr)[j as int],
        arr[j as int] == old(arr)[i as int],
        forall|k: int| 0 <= k < arr.len() && ({k != i as int && k != j as int}) ==> arr[k] == old(arr)[k],
        arr@.to_multiset() == old(arr)@.to_multiset(),
        arr.len() == old(arr).len(),
{
    let old_arr_val = arr@;
    let temp = arr[i];
    arr.set(i, arr[j]);
    arr.set(j, temp);

    proof {
        swap_properties(old_arr_val, i, j, arr@);
    }
}

proof fn relative_order_helper(original_seq: Seq<i32>, current_seq: Seq<i32>, old_current_seq_at_entry: Seq<i32>,
    updated_current_non_zero_idx: int, old_current_non_zero_idx: int,
    i_val: int, swap_i: usize, swap_j: usize)
    requires
        original_seq.len() == current_seq.len(),
        current_seq.to_multiset() == original_seq.to_multiset(),

        old_current_non_zero_idx <= i_val,
        old_current_non_zero_idx <= original_seq.len(),
        0 <= updated_current_non_zero_idx <= current_seq.len(),

        // Property from previous iteration's invariant:
        // Relative order for elements before `i_val`.
        forall|n: int, m: int| 0 <= n < m < i_val && original_seq[n] != 0 && original_seq[m] != 0 ==>
            exists|k_idx: int, l_idx: int| 0 <= k_idx < l_idx < old_current_non_zero_idx && old_current_seq_at_entry.index(k_idx) == original_seq[n] && old_current_seq_at_entry.index(l_idx) == original_seq[m],
        
        // Relationship between current_seq and old(current_seq) for swap_elem
        current_seq.index(swap_i as int) == old_current_seq_at_entry[swap_j as int],
        current_seq.index(swap_j as int) == old_current_seq_at_entry[swap_i as int],
        forall |k: int| 0 <= k < current_seq.len() && k != swap_i as int && k != swap_j as int ==> current_seq.index(k) == old_current_seq_at_entry.index(k),
        
        // In this case, `swap_i` is `i_val` and `swap_j` is `old_current_non_zero_idx`.
        swap_i == i_val as usize,
        swap_j == old_current_non_zero_idx as usize,
        
        // Before swap, current_seq[old_current_non_zero_idx] was 0
        old_current_seq_at_entry.index(old_current_non_zero_idx) == 0,
        // Before swap, current_seq[i_val] was non-zero
        old_current_seq_at_entry.index(i_val) != 0,
    
    ensures
        // Relative order for elements up to `i_val + 1`.
        forall|n: int, m: int| 0 <= n < m < i_val + 1 && original_seq[n] != 0 && original_seq[m] != 0 ==>
            exists|k_idx: int, l_idx: int| 0 <= k_idx < l_idx < updated_current_non_zero_idx && current_seq.index(k_idx) == original_seq[n] && current_seq.index(l_idx) == original_seq[m],
{}
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
    let len = arr.len();
    if len < 2 { return }

    let mut current_non_zero_idx: int = 0;
    let old_arr_seq = arr@;

    let mut i = 0_usize;
    while i < len
        invariant
            len == old(arr).len(),
            current_non_zero_idx <= i,
            current_non_zero_idx <= len,
            arr@.to_multiset() == old_arr_seq.to_multiset(),

            // All elements before `current_non_zero_idx` are non-zero.
            forall|p: int| 0 <= p < current_non_zero_idx ==> arr[p] != 0,
            // All elements between `current_non_zero_idx` and `i` (exclusive) are zero.
            forall|p: int| current_non_zero_idx <= p < i ==> arr[p] == 0,

            // Relative order of non-zero elements encountered so far:
            // For any `n, m` such that `0 <= n < m < i` and `old_arr_seq[n] != 0` and `old_arr_seq[m] != 0`,
            // there exist `k_idx, l_idx` such that `0 <= k_idx < l_idx < current_non_zero_idx` and
            // `arr[k_idx] == old_arr_seq[n]` and `arr[l_idx] == old_arr_seq[m]`,
            forall|n: int, m: int| 0 <= n < m < i && old_arr_seq[n] != 0 && old_arr_seq[m] != 0 ==>
                exists|k_idx: int, l_idx: int| 0 <= k_idx < l_idx < current_non_zero_idx && arr[k_idx] == old_arr_seq[n] && arr[l_idx] == old_arr_seq[m],

            // The number of zeros in `arr[0..i]` is the same as in `old_arr_seq[0..i]`.
            count_zeros_in_range(arr@, 0, i) == count_zeros_in_range(old_arr_seq, 0, i),
            // No zeros appear before `current_non_zero_idx`.
            count_zeros_in_range(arr@, 0, current_non_zero_idx) == 0,
            // All elements between `current_non_zero_idx` and `i` are zeros,
            // and their count matches the zeros encountered in `old_arr_seq[0..i]` that are not yet moved to non-zero part.
            count_zeros_in_range(arr@, current_non_zero_idx, i) == i - current_non_zero_idx,

            // The number of zeros in `old_arr_seq` up to `i` is equal to the number of zeros encountered and moved.
            count_zeros_in_range(old_arr_seq, 0, i) == (i - current_non_zero_idx) + count_zeros_in_range(old_arr_seq, 0, current_non_zero_idx),
    {
        if arr[i] != 0 {
            if i as int != current_non_zero_idx {
                let _old_arr_at_i = arr[i];
                let _old_arr_at_cnzi = arr[current_non_zero_idx as usize];
                let pre_swap_arr_seq = arr@;

                swap_elem(arr, i, current_non_zero_idx as usize);

                proof {
                    let next_current_non_zero_idx = current_non_zero_idx + 1;
                    assert(arr.len() == old_arr_seq.len());
                    assert(arr@.to_multiset() == old_arr_seq.to_multiset());

                    // Preserve non-zero property before current_non_zero_idx
                    // Elements from `0` to `current_non_zero_idx-1` are not affected by swap_elem(i, current_non_zero_idx).
                    forall|p: int| 0 <= p < current_non_zero_idx implies arr[p] != 0 by {
                        if p != current_non_zero_idx && p != i as int {
                            assert(arr[p] == pre_swap_arr_seq[p]);
                            assert(pre_swap_arr_seq[p] != 0); // From loop invariant
                        } else if p == current_non_zero_idx {
                            // This path is not taken, p < current_non_zero_idx
                            assert(false);
                        } else if p == i as int {
                            // This path is not taken, p < current_non_zero_idx and current_non_zero_idx <= i
                            assert(false);
                        }
                    }
                    assert(arr[current_non_zero_idx as int] == _old_arr_at_i);
                    assert(_old_arr_at_i != 0);

                    // Preserve zero-property between `current_non_zero_idx+1` and `i+1` (exclusive, so up to `i`)
                    // The original `arr[current_non_zero_idx]` (which was 0) is now at `arr[i]`.
                    // Other elements `arr[p]` for `current_non_zero_idx < p < i` are unchanged and are 0.
                    forall|p: int| current_non_zero_idx < p < i + 1 implies arr[p] == 0 by {
                        if p == i as int {
                            assert(arr[p] == _old_arr_at_cnzi);
                            assert(_old_arr_at_cnzi == 0);
                        } else {
                            assert(arr[p] == pre_swap_arr_seq[p]);
                            assert(pre_swap_arr_seq[p] == 0);
                        }
                    }

                    // Relative order of non-zero elements
                    relative_order_helper(old_arr_seq, arr@, pre_swap_arr_seq, next_current_non_zero_idx, current_non_zero_idx, i as int, i, current_non_zero_idx as usize);
                    
                    // Count zeros invariants for next iteration
                    // After swap: `arr[current_non_zero_idx]` is `_old_arr_at_i` (non-zero). `arr[i]` is `_old_arr_at_cnzi` (zero).
                    assert(count_zeros_in_range(arr@, 0, next_current_non_zero_idx) == 0) by {
                        assert(count_zeros_in_range(arr@, 0, current_non_zero_idx) == 0); // From loop invariant for pre_swap_arr_seq
                        assert(arr[current_non_zero_idx as int] != 0); // As _old_arr_at_i != 0
                    }

                    assert(count_zeros_in_range(arr@, next_current_non_zero_idx, i + 1) == (i + 1) - next_current_non_zero_idx) by {
                        // All elements from `original current_non_zero_idx+1` to `original i-1` were 0 and are unchanged.
                        // The element at `original current_non_zero_idx` (which was 0) is now at `i`.
                        // So from `next_current_non_zero_idx` to `i+1` (exclusive), elements are 0.
                        let prev_cnzi_plus_1 = current_non_zero_idx + 1;
                        forall|p: int| prev_cnzi_plus_1 <= p < i + 1 implies arr[p] == 0 by {
                            if p == i as int {
                                assert(arr[p] == _old_arr_at_cnzi);
                                assert(_old_arr_at_cnzi == 0);
                            } else {
                                assert(arr[p] == pre_swap_arr_seq[p]);
                                assert(pre_swap_arr_seq[p] == 0);
                            }
                        }
                    }

                    let next_i_plus_1 = i + 1;
                    assert(count_zeros_in_range(arr@, 0, next_i_plus_1) == count_zeros_in_range(old_arr_seq, 0, next_i_plus_1)) by {
                        count_zeros_in_range_split(arr@, 0, next_current_non_zero_idx, next_i_plus_1);
                        assert(count_zeros_in_range(arr@, 0, next_i_plus_1) == count_zeros_in_range(arr@, 0, next_current_non_zero_idx) + count_zeros_in_range(arr@, next_current_non_zero_idx, next_i_plus_1));
                        assert(count_zeros_in_range(arr@, 0, next_i_plus_1) == 0 + ((i + 1) - (current_non_zero_idx + 1)));
                        assert(count_zeros_in_range(arr@, 0, next_i_plus_1) == i - current_non_zero_idx);

                        assert(old_arr_seq[i as int] != 0); // Given `arr[i]` != 0 initially
                        assert(count_zeros_in_range(old_arr_seq, 0, next_i_plus_1) == count_zeros_in_range(old_arr_seq, 0,i) + (if old_arr_seq[i as int] == 0 { 1 } else { 0 }));
                        assert(count_zeros_in_range(old_arr_seq, 0, next_i_plus_1) == count_zeros_in_range(old_arr_seq, 0,i)); // because old_arr_seq[i] != 0

                        assert(count_zeros_in_range(old_arr_seq, 0, i) == (i - current_non_zero_idx) + count_zeros_in_range(old_arr_seq, 0, current_non_zero_idx)); // from invariant
                        assert(count_zeros_in_range(old_arr_seq, 0, current_non_zero_idx) == 0); // From invariant 
                    }
                }
            }
            current_non_zero_idx = current_non_zero_idx + 1;
        } else {
            // arr[i] == 0, leave it there.
            proof {
                // The non-zero property before `current_non_zero_idx` is unchanged.
                forall|p: int| 0 <= p < current_non_zero_idx implies arr[p] != 0 by {
                    assert(arr[p] == old(arr)[p]);
                    assert(old(arr)[p] != 0);
                }

                // The zero property between `current_non_zero_idx` and `i+1`
                // `arr[current_non_zero_idx..i]` were zeros from loop invariant.
                // `arr[i]` is also zero by the `if` condition. So `arr[current_non_zero_idx..i+1]` are zeros.
                forall|p: int| current_non_zero_idx <= p < i + 1 implies arr[p] == 0 by {
                    if p == i as int {
                        assert(arr[p] == 0);
                    } else {
                        assert(arr[p] == old(arr)[p]);
                        assert(old(arr)[p] == 0);
                    }
                }

                // Relative order of non-zero elements is unchanged as `current_non_zero_idx` does not move.
                // And we are adding a zero element to the considered range, which does not violate the condition.
                forall|n: int, m: int| 0 <= n < m < i + 1 && old_arr_seq[n] != 0 && old_arr_seq[m] != 0 ==>
                    exists|k_idx: int, l_idx: int| 0 <= k_idx < l_idx < current_non_zero_idx && arr[k_idx] == old_arr_seq[n] && arr[l_idx] == old_arr_seq[m]
                by {
                    if m < i as int {
                        // This case is covered by the invariant in the previous iteration
                        assert(exists|k_idx_v: int, l_idx_v: int| 0 <= k_idx_v < l_idx_v < current_non_zero_idx && old(arr)[k_idx_v] == old_arr_seq[n] && old(arr)[l_idx_v] == old_arr_seq[m]);
                        let k_idx_val = choose|k_v: int| 0 <= k_v < current_non_zero_idx && old(arr)[k_v] == old_arr_seq[n];
                        let l_idx_val = choose|l_v: int| k_idx_val < l_v < current_non_zero_idx && old(arr)[l_v] == old_arr_seq[m];
                        assert(arr[k_idx_val] == old(arr)[k_idx_val]);
                        assert(arr[l_idx_val] == old(arr)[l_idx_val]);
                    }
                    else { // m == i, and old_arr_seq[i] must be 0 for this branch. So premise (`old_arr_seq[m] != 0`) is false anyway.
                           // The if block `arr[i] != 0` handles the non-zero case.
                           // So if we are in this `else` block, `arr[i]` must be 0.
                           // Since `arr@.to_multiset() == old_arr_seq.to_multiset()` and `arr[k] == old(arr)[k]` for k != i,
                           // it indicates `old_arr_seq[i]` must also be 0 in this branch.
                           // Thus `old_arr_seq[m] != 0` (where `m=i`) is false.
                        assert(old_arr_seq[i as int] == 0); // This assertion is implied for the premise `old_arr_seq[m] != 0` to be false.
                    }
                }

                // Count zeros invariants for next iteration
                assert(count_zeros_in_range(arr@, 0, i + 1) == count_zeros_in_range(old_arr_seq, 0, i + 1)) by {
                    assert(count_zeros_in_range(arr@, 0, i) == count_zeros_in_range(old_arr_seq, 0, i)); // From loop invariant
                    assert(arr[i as int] == 0);
                    assert(old_arr_seq[i as int] == 0); // This follows from arr[i] == 0 and multiset equality
                    assert(count_zeros_in_range(arr@, 0, i + 1) == count_zeros_in_range(arr@, 0, i) + 1);
                    assert(count_zeros_in_range(old_arr_seq, 0, i + 1) == count_zeros_in_range(old_arr_seq, 0, i) + 1);
                }
                assert(count_zeros_in_range(arr@, 0, current_non_zero_idx) == 0);
                assert(count_zeros_in_range(arr@, current_non_zero_idx, i + 1) == (i + 1) - current_non_zero_idx); // The actual number of zeros now
                assert(count_zeros_in_range(old_arr_seq, 0, i + 1) == (i + 1 - current_non_zero_idx) + count_zeros_in_range(old_arr_seq, 0, current_non_zero_idx));
            }
        }
        i = i + 1;
    }

    // Post-loop assertions
    // All non-zero elements are at the beginning, followed by all zeros.
    assert(forall|p: int| 0 <= p < current_non_zero_idx ==> arr[p] != 0);
    assert(forall|p: int| current_non_zero_idx <= p < len ==> arr[p] == 0);

    // Consequence of invariant 4: Zeros to the right of the first zero
    // For any `j` such that `current_non_zero_idx <= j < len`, `arr[j]` is 0.
    // So if `arr[idx_first_zero]` is the first zero, then `idx_first_zero == current_non_zero_idx`.
    // Then for any `i: int, j: int| 0 <= i < j < arr.len() && arr[i] == 0`, we must have `i >= current_non_zero_idx`.
    // Thus `j` must also be `>= current_non_zero_idx`, which means `arr[j]` is 0.
    assert(forall|n: int, m: int| 0 <= n < m < arr.len() && arr[n] == 0 ==> arr[m] == 0) by {
        let first_zero_idx = current_non_zero_idx;
        forall|n: int, m: int| 0 <= n < m < arr.len() && arr[n] == 0 implies arr[m] == 0 {
            assert(n >= first_zero_idx); // Because elements before first_zero_idx are non-zero (from invariant).
            assert(m >= first_zero_idx); // Because m > n and n >= first_zero_idx.
            assert(arr[m] == 0); // From the post-loop assertion `forall|p: int| current_non_zero_idx <= p < len ==> arr[p] == 0`.
        }
    }

    // Preserve the number of non-zero elements and zeros.
    assert(count_zeros_in_range(arr@, 0, len) == count_zeros_in_range(old_arr_seq, 0, len));

    // The final array is a permutation of the original one (already covered by multiset equality)
    assert(arr@.to_multiset() == old_arr_seq.to_multiset());

    // Relative order of non-zero elements is preserved
    assert(forall|n: int, m: int| 0 <= n < m < old_arr_seq.len() && old_arr_seq[n] != 0 && old_arr_seq[m] != 0 ==>
        exists|k: int, l: int| 0 <= k < l < arr.len() && arr[k] == old_arr_seq[n] && arr[l] == old_arr_seq[m]) by {
        forall|n: int, m: int| 0 <= n < m < old_arr_seq.len() && old_arr_seq[n] != 0 && old_arr_seq[m] != 0 implies
            exists|k: int, l: int| 0 <= k < l < arr.len() && arr[k] == old_arr_seq[n] && arr[l] == old_arr_seq[m]
        {
            // The loop invariant `forall|n: int, m: int| 0 <= n < m < i && old_arr_seq[n] != 0 && old_arr_seq[m] != 0 ==> ...`
            // holds for `i = len` at the end of the loop, which is exactly the post-condition.
            assert(current_non_zero_idx <= arr.len());
            assert(exists|k: int, l: int| 0 <= k < l < current_non_zero_idx && arr[k] == old_arr_seq[n] && arr[l] == old_arr_seq[m]);
            let k_idx = choose|k_v: int| 0 <= k_v < current_non_zero_idx && arr[k_v] == old_arr_seq[n];
            let l_idx = choose|l_v: int| k_idx < l_v < current_non_zero_idx && arr[l_v] == old_arr_seq[m];
            assert(0 <= k_idx < l_idx < current_non_zero_idx);
            assert(l_idx < arr.len());
        }
    }
}
// </vc-code>

fn main() {}

}