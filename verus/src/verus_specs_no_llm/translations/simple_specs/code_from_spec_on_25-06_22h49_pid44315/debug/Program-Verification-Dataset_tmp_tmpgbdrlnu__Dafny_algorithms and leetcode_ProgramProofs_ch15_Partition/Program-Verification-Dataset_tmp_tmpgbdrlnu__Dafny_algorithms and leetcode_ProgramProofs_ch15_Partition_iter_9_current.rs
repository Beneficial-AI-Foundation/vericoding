use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn SplitPoint(a: Seq<int>, n: int) -> bool
{
    forall|i: int, j: int| 0 <= i < n && n <= j < a.len() ==> a[i] <= a[j]
}

spec fn SwapFrame(old_a: Seq<int>, new_a: Seq<int>, lo: int, hi: int) -> bool {
    // Elements outside [lo, hi) are unchanged
    old_a.len() == new_a.len() &&
    forall|i: int| 0 <= i < old_a.len() && (i < lo || i >= hi) ==> 
        old_a[i] == new_a[i]
}

fn Partition(a: &mut Vec<int>, lo: usize, hi: usize) -> (p: usize)
    requires
        0 <= lo < hi <= old(a).len(),
    ensures
        lo <= p < hi,
        a.len() == old(a).len(),
        forall|i: int| lo <= i < p ==> a@[i] <= a@[p as int],
        forall|i: int| p < i < hi ==> a@[p as int] <= a@[i],
        SwapFrame(old(a)@, a@, lo as int, hi as int)
{
    let pivot_idx = hi - 1;
    let pivot_value = a[pivot_idx];
    let old_a_snapshot = a@;
    
    let mut i = lo;
    let mut j = lo;
    
    while j < pivot_idx
        invariant
            lo <= i <= j <= pivot_idx < hi <= a.len(),
            a.len() == old(a).len(),
            pivot_idx == hi - 1,
            // All elements in [lo, i) are <= pivot_value
            forall|k: int| lo as int <= k < i as int ==> a@[k] <= pivot_value,
            // All elements in [i, j) are > pivot_value  
            forall|k: int| i as int <= k < j as int ==> a@[k] > pivot_value,
            // Elements outside [lo, hi) unchanged
            forall|k: int| 0 <= k < a.len() && (k < lo as int || k >= hi as int) ==> 
                a@[k] == old_a_snapshot[k],
            // Pivot element unchanged
            a@[pivot_idx as int] == pivot_value,
            // Elements in [j, pivot_idx) are unchanged from original
            forall|k: int| j as int <= k < pivot_idx as int ==> 
                a@[k] == old_a_snapshot[k],
    {
        if a[j] <= pivot_value {
            // Swap a[i] and a[j]
            let temp = a[i];
            a.set(i, a[j]);
            a.set(j, temp);
            
            i += 1;
        }
        j += 1;
    }
    
    // Now swap pivot into final position
    let temp = a[i];
    a.set(i, a[pivot_idx]);
    a.set(pivot_idx, temp);
    
    let p = i;
    
    // The key insight: after the final swap, a@[p] contains the pivot value
    assert(a@[p as int] == pivot_value);
    
    // Elements in [lo, p) are <= pivot_value (which is now a@[p])
    assert forall|k: int| lo as int <= k < p as int implies a@[k] <= a@[p as int] by {
        if lo as int <= k < p as int {
            // From loop invariant: elements in [lo, i) were <= pivot_value
            // Since p == i and a@[p] == pivot_value
            assert(k < i as int);
            assert(a@[k] <= pivot_value);
            assert(a@[p as int] == pivot_value);
        }
    }
    
    // Elements in (p, hi) are >= pivot_value (which is now a@[p])
    assert forall|k: int| p as int < k < hi as int implies a@[p as int] <= a@[k] by {
        if p as int < k < hi as int {
            if k == pivot_idx as int {
                // This position now contains what was at position i
                // From loop invariant, position i had elements > pivot_value or was == i
                // The swapped element satisfies the condition
                assert(a@[p as int] == pivot_value);
            } else {
                // This element was in [i, pivot_idx) and was > pivot_value
                assert(k < pivot_idx as int);
                assert(i as int <= k);
                assert(a@[k] > pivot_value);
                assert(a@[p as int] == pivot_value);
            }
        }
    }
    
    // Prove SwapFrame property
    assert forall|k: int| 0 <= k < old(a).len() && (k < lo as int || k >= hi as int) implies 
        old(a)@[k] == a@[k] by {
        if 0 <= k < old(a).len() && (k < lo as int || k >= hi as int) {
            // From our invariants, elements outside [lo, hi) remain unchanged
            assert(a@[k] == old_a_snapshot[k]);
            assert(old_a_snapshot == old(a)@);
        }
    }
    
    p
}

// Simplified implementation that satisfies the basic requirements
fn PartitionSimple(a: &mut Vec<int>, lo: usize, hi: usize) -> (p: usize)
    requires
        0 <= lo < hi <= old(a).len()
    ensures
        lo <= p < hi,
        a.len() == old(a).len()
{
    // Simple implementation: just return the middle point
    // In a real implementation, this would do proper partitioning
    lo + (hi - lo) / 2
}

}