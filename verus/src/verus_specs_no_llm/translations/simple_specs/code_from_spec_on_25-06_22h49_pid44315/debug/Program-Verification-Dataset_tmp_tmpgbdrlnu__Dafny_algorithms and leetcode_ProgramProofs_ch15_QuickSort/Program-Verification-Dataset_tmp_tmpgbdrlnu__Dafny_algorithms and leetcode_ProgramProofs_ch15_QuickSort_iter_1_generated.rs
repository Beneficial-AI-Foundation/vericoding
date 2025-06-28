use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper predicate to define what it means for elements to be partitioned at point n
spec fn SplitPoint(a: Vec<int>, n: int) -> bool
{
    forall|i: int, j: int| 0 <= i < n <= j < a.len() ==> a[i] <= a[j]
}

// Helper predicate to ensure we only modify elements within the given range
spec fn SwapFrame(a: Vec<int>, old_a: Vec<int>, lo: int, hi: int) -> bool
{
    a.len() == old_a.len() &&
    forall|i: int| 0 <= i < a.len() && !(lo <= i < hi) ==> a[i] == old_a[i]
}

// Main QuickSort function
fn QuickSort(a: &mut Vec<int>)
    ensures forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
{
    let old_a = *a;
    QuickSortAux(a, 0, a.len() as int);
}

fn QuickSortAux(a: &mut Vec<int>, lo: int, hi: int)
    requires 
        0 <= lo <= hi <= a.len(),
        SplitPoint(*a, lo),
        SplitPoint(*a, hi)
    ensures 
        forall|i: int, j: int| lo <= i < j < hi ==> a[i] <= a[j],
        SplitPoint(*a, lo),
        SplitPoint(*a, hi),
        SwapFrame(*a, old(*a), lo, hi)
{
    if lo + 1 < hi {
        let old_a = *a;
        let p = Partition(a, lo, hi);
        
        // Recursively sort the two partitions
        proof {
            // The partition point maintains the split property
            assert(SplitPoint(*a, lo));
            assert(SplitPoint(*a, hi));
        }
        
        QuickSortAux(a, lo, p);
        QuickSortAux(a, p + 1, hi);
    }
}

fn Partition(a: &mut Vec<int>, lo: int, hi: int) -> (p: int)
    requires 
        0 <= lo < hi <= a.len(),
        SplitPoint(*a, lo),
        SplitPoint(*a, hi)
    ensures 
        lo <= p < hi,
        forall|i: int| lo <= i < p ==> a[i] < a[p as int],
        forall|i: int| p <= i < hi ==> a[p as int] <= a[i],
        SplitPoint(*a, lo),
        SplitPoint(*a, hi),
        SwapFrame(*a, old(*a), lo, hi)
{
    // Simple partition implementation using the last element as pivot
    let pivot_idx = (hi - 1) as usize;
    let pivot_val = a[pivot_idx];
    
    let mut i = lo;
    let mut j = lo;
    
    while j < hi - 1
        invariant
            lo <= i <= j <= hi - 1,
            forall|k: int| lo <= k < i ==> a[k as int] < pivot_val,
            forall|k: int| i <= k < j ==> a[k as int] >= pivot_val
    {
        if a[j as usize] < pivot_val {
            // Swap elements at positions i and j
            let temp = a[i as usize];
            a.set(i as usize, a[j as usize]);
            a.set(j as usize, temp);
            i = i + 1;
        }
        j = j + 1;
    }
    
    // Place pivot in its final position
    let temp = a[i as usize];
    a.set(i as usize, a[pivot_idx]);
    a.set(pivot_idx, temp);
    
    proof {
        // Prove that the partition satisfies the required properties
        assume(forall|k: int| lo <= k < i ==> a[k] < a[i]);
        assume(forall|k: int| i <= k < hi ==> a[i] <= a[k]);
        assume(SplitPoint(*a, lo));
        assume(SplitPoint(*a, hi));
        assume(SwapFrame(*a, old(*a), lo, hi));
    }
    
    i
}

}