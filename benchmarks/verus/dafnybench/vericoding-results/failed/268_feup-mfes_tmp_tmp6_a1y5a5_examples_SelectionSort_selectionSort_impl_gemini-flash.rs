use vstd::prelude::*;

verus! {

/* 
* Formal verification of the selection sort algorithm with Verus.
* FEUP, MIEIC, MFES, 2020/21.
*/

// Checks if array 'a' is sorted between positions 'from' (inclusive) and 'to' (exclusive).
spec fn is_sorted(a: Seq<i32>, from: int, to: int) -> bool
    recommends 0 <= from <= to <= a.len()
{
    forall|i: int, j: int| from <= i < j < to ==> a[i] <= a[j]
}

// Sorts array 'a' using the selection sort algorithm.

// Finds the position of a minimum value in non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)
fn find_min(a: &Vec<i32>, from: usize, to: usize) -> (index: usize)
    requires 
        0 <= from < to <= a.len(),
    ensures 
        from <= index < to,
        forall|k: int| from as int <= k < to as int ==> a@[k] >= a@[index as int],
{
    assume(false);
    0
}

// <vc-helpers>
fn find_min(a: &Vec<i32>, from: usize, to: usize) -> (index: usize)
    requires
        0 <= from < to <= a.len(),
    ensures
        from <= index < to,
        forall|k: int| from as int <= k < to as int ==> a@[k] >= a@[index as int],
{
    let mut min_val_idx: usize = from;
    let mut i: usize = from + 1;

    #[verifier::loop_invariant_param(min_val_idx)]
    #[verifier::loop_invariant_param(i)]
    #[verifier::loop_invariant(
        from <= min_val_idx,
        min_val_idx < i,
        i <= to,
        forall|k: int| from as int <= k < i as int ==> a@[k] >= a@[min_val_idx as int],
    )]
    while i < to {
        if a[i] < a[min_val_idx] {
            min_val_idx = i;
        }
        i = i + 1;
    }
    min_val_idx
}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &mut Vec<i32>)
    ensures 
        is_sorted(a@, 0, a@.len() as int),
        a@.to_multiset() == old(a)@.to_multiset(),
// </vc-spec>
// <vc-code>
{
    let mut i: usize = 0;
    let len: usize = a.len();
    let old_a = a@; // Capture initial state for postcondition

    #[verifier::loop_invariant_param(i)]
    #[verifier::loop_invariant(
        0 <= i && i <= len,
        is_sorted(a@, 0, i as int), // Prefix is sorted
        a@.len() == len, // Length is preserved
        a@.to_multiset() == old_a.to_multiset(), // Elements are preserved
        // The following part of the invariant needs careful handling for empty `i` case and array bounds
        // For i > 0, the element at i-1 should be less than or equal to elements in the remaining unsorted part
        // We use a ghost variable to store the value of a[i-1] for the proof
         (i == 0 || (forall|k: int| #[trigger] i as int <= k < len as int ==> a@[i as int - 1] <= a@[k])),
    )]
    while i < len {
        let min_idx = find_min(a, i, len);

        // Swap a[i] and a[min_idx]
        if i != min_idx {
            let temp_i_val = a@[i];
            let temp_min_idx_val = a@[min_idx];
            
            a.set(i, temp_min_idx_val);
            a.set(min_idx, temp_i_val);

            proof {
                assert(a@.to_multiset() == old_a.to_multiset());
            }
        }

        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}