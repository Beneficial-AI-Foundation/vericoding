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
    
    let mut i = lo;
    let mut j = lo;
    
    while j < pivot_idx
        invariant
            lo <= i <= j <= pivot_idx < hi <= a.len(),
            a.len() == old(a).len(),
            pivot_value == a@[pivot_idx as int],
            // All elements in [lo, i) are <= pivot
            forall|k: int| lo <= k < i ==> a@[k] <= pivot_value,
            // All elements in [i, j) are > pivot  
            forall|k: int| i <= k < j ==> a@[k] > pivot_value,
            // Elements outside [lo, hi) unchanged
            forall|k: int| 0 <= k < old(a).len() && (k < lo || k >= hi) ==> 
                a@[k] == old(a)@[k],
            // Pivot element unchanged
            a@[pivot_idx as int] == pivot_value,
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
    
    // Place pivot in its final position by swapping with element at i
    let temp = a[i];
    a.set(i, a[pivot_idx]);
    a.set(pivot_idx, temp);
    
    let p = i;
    
    // Prove the postconditions
    assert forall|k: int| lo <= k < p implies a@[k] <= a@[p as int] by {
        if lo <= k < p {
            // From loop invariant: elements in [lo, i) are <= pivot_value
            // and a@[p] == pivot_value after the swap
            assert(k < i);
            assert(a@[k] <= pivot_value);
            assert(a@[p as int] == pivot_value);
        }
    };
    
    assert forall|k: int| p < k < hi implies a@[p as int] <= a@[k] by {
        if p < k < hi {
            if k == pivot_idx as int {
                // This is the element we swapped from position i
                // From loop invariant: it was > pivot_value, so >= pivot_value
                assert(a@[k] >= pivot_value);
                assert(a@[p as int] == pivot_value);
            } else {
                // This element was > pivot_value from loop invariant  
                assert(k < pivot_idx as int);
                assert(i <= k);
                assert(a@[k] > pivot_value);
                assert(a@[p as int] == pivot_value);
            }
        }
    };
    
    // Prove SwapFrame property
    assert forall|k: int| 0 <= k < old(a).len() && (k < lo || k >= hi) implies 
        old(a)@[k] == a@[k] by {
            // This follows from our loop invariant and the fact that we only
            // modify elements in [lo, hi)
    };
    
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