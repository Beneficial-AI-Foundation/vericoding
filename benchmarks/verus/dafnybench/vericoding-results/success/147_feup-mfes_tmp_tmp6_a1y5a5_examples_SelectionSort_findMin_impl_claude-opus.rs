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

// </vc-helpers>

// <vc-spec>
fn find_min(a: &mut [i32], from: usize, to: usize) -> (index: usize)
    requires 
        0 <= from < to <= old(a).len(),
    ensures
        from <= index < to,
        forall|k: int| from <= k < to ==> old(a)[k] >= old(a)[index as int],
// </vc-spec>
// <vc-code>
{
    let mut min_idx: usize = from;
    let mut i: usize = from + 1;
    
    while i < to
        invariant
            from <= min_idx < to,
            from < i <= to,
            min_idx < a.len(),
            i <= a.len(),
            to <= a.len(),
            forall|k: int| from <= k < i ==> k < a.len() && a[k] >= a[min_idx as int],
        decreases to - i,
    {
        assert(i < to);
        assert(to <= a.len());
        assert(i < a.len());
        assert(min_idx < a.len());
        
        if a[i] < a[min_idx] {
            min_idx = i;
        }
        i = i + 1;
    }
    
    min_idx
}
// </vc-code>

fn main() {
}

}