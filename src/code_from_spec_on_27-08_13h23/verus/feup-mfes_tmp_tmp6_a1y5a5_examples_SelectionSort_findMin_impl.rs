use vstd::prelude::*;

verus! {

/* 
 * Formal verification of the selection sort algorithm with Verus.
 * FEUP, MIEIC, MFES, 2020/21.
 */

// Checks if array 'a' is sorted between positions 'from' (inclusive) and 'to' (exclusive).
pub open spec fn is_sorted(a: &[i32], from: usize, to: usize) -> bool {
    &&& from <= to <= a.len()
    &&& forall|i: int, j: int| from <= i < j < to ==> a[i] <= a[j]
}

// Sorts array 'a' using the selection sort algorithm.

// Finds the position of a minimum value in non-empty subarray 'a' between positions 
// 'from' (inclusive) and 'to' (exclusive)

// <vc-helpers>
pub open spec fn is_min(a: &[i32], from: usize, to: usize, min_idx: usize) -> bool {
    &&& from <= min_idx < to
    &&& forall|k: int| from <= k < to ==> a[k] >= a[min_idx]
}

proof fn lemma_min_idx(a: &[i32], from: usize, to: usize, curr_min: usize, i: usize)
    requires
        from <= curr_min < to,
        from <= i < to,
        is_min(a, from, i, curr_min),
        a[i] < a[curr_min],
    ensures
        is_min(a, from, i + 1, i),
{
}

proof fn lemma_min_idx_unchanged(a: &[i32], from: usize, to: usize, curr_min: usize, i: usize)
    requires
        from <= curr_min < to,
        from <= i < to,
        is_min(a, from, i, curr_min),
        a[i] >= a[curr_min],
    ensures
        is_min(a, from, i + 1, curr_min),
{
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn find_min(a: &mut [i32], from: usize, to: usize) -> (index: usize)
    requires 
        0 <= from < to <= old(a).len(),
    ensures
        from <= index < to,
        forall|k: int| from <= k < to ==> old(a)[k] >= old(a)[index as int],
// </vc-spec>
// </vc-spec>

// <vc-code>
fn find_min(a: &mut [i32], from: usize, to: usize) -> (index: usize)
    requires
        0 <= from < to <= a.len(),
    ensures
        from <= index < to,
        forall|k: int| from <= k < to ==> a[k] >= a[index],
{
    let mut min_idx = from;
    let mut i = from + 1;

    while i < to
        invariant
            from <= min_idx < to,
            from <= i <= to,
            is_min(a, from, i, min_idx),
    {
        if a[i] < a[min_idx] {
            min_idx = i;
            proof {
                lemma_min_idx(a, from, to, min_idx, i);
            }
        } else {
            proof {
                lemma_min_idx_unchanged(a, from, to, min_idx, i);
            }
        }
        i = i + 1;
    }

    min_idx
}
// </vc-code>

fn main() {
}

}