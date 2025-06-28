use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper predicate to define what it means for elements to be partitioned at point n
spec fn SplitPoint(a: Vec<int>, n: int) -> bool
{
    forall|i: int, j: int| 0 <= i < n && n <= j < a.len() ==> a[i] <= a[j]
}

// Helper predicate to ensure we only modify elements within the given range
spec fn SwapFrame(a: Vec<int>, old_a: Vec<int>, lo: int, hi: int) -> bool
{
    a.len() == old_a.len() &&
    forall|i: int| 0 <= i < a.len() && (i < lo || i >= hi) ==> a[i] == old_a[i]
}

// Main QuickSort function
fn QuickSort(a: &mut Vec<int>)
    ensures forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
{
    if a.len() > 1 {
        QuickSortAux(a, 0, a.len() as int);
    }
}

fn QuickSortAux(a: &mut Vec<int>, lo: int, hi: int)
    requires 
        0 <= lo <= hi <= a.len()
    ensures 
        forall|i: int, j: int| lo <= i < j < hi ==> a[i] <= a[j],
        a.len() == old(a).len(),
        forall|i: int| 0 <= i < a.len() && (i < lo || i >= hi) ==> a[i] == old(a)[i]
    decreases hi - lo
{
    if lo + 1 < hi {
        let p = Partition(a, lo, hi);
        
        assert(lo <= p < hi);
        assert(forall|i: int| lo <= i < p ==> a[i] <= a[p]);
        assert(forall|i: int| p < i < hi ==> a[p] <= a[i]);
        
        QuickSortAux(a, lo, p);
        QuickSortAux(a, p + 1, hi);
        
        // Proof that the entire range is now sorted
        assert(forall|i: int, j: int| lo <= i < j < hi ==> a[i] <= a[j]) by {
            assert(forall|i: int, j: int| lo <= i < j < p ==> a[i] <= a[j]);
            assert(forall|i: int, j: int| p + 1 <= i < j < hi ==> a[i] <= a[j]);
            assert(forall|i: int| lo <= i < p ==> a[i] <= a[p]);
            assert(forall|i: int| p < i < hi ==> a[p] <= a[i]);
        }
    }
}

fn Partition(a: &mut Vec<int>, lo: int, hi: int) -> (p: int)
    requires 
        0 <= lo < hi <= a.len()
    ensures 
        lo <= p < hi,
        forall|i: int| lo <= i < p ==> a[i] <= a[p],
        forall|i: int| p < i < hi ==> a[p] <= a[i],
        a.len() == old(a).len(),
        forall|i: int| 0 <= i < a.len() && (i < lo || i >= hi) ==> a[i] == old(a)[i]
{
    // Simple partition implementation using the last element as pivot
    let pivot_idx = hi - 1;
    let pivot_val = a[pivot_idx as usize];
    
    let mut i = lo;
    let mut j = lo;
    
    while j < hi - 1
        invariant
            lo <= i <= j <= hi - 1,
            lo < hi <= a.len(),
            pivot_idx == hi - 1,
            a[pivot_idx as usize] == pivot_val,
            forall|k: int| lo <= k < i ==> a[k as usize] <= pivot_val,
            forall|k: int| i <= k < j ==> a[k as usize] > pivot_val,
            a.len() == old(a).len(),
            forall|k: int| 0 <= k < a.len() && (k < lo || k >= hi) ==> a[k as usize] == old(a)[k as usize]
    {
        if a[j as usize] <= pivot_val {
            // Swap elements at positions i and j
            if i != j {
                let temp = a[i as usize];
                a.set(i as usize, a[j as usize]);
                a.set(j as usize, temp);
            }
            i = i + 1;
        }
        j = j + 1;
    }
    
    // Place pivot in its final position
    let temp = a[i as usize];
    a.set(i as usize, a[pivot_idx as usize]);
    a.set(pivot_idx as usize, temp);
    
    // Proof assertions to help verification
    assert(lo <= i < hi);
    
    // Prove the partition property
    assert(forall|k: int| lo <= k < i ==> a[k as usize] <= a[i as usize]) by {
        // All elements from lo to i-1 were <= pivot_val in the loop
        // a[i] now contains the pivot_val
        assert(a[i as usize] == pivot_val);
    }
    
    assert(forall|k: int| i < k < hi ==> a[i as usize] <= a[k as usize]) by {
        // For positions after i, we need to consider two cases:
        // 1. For k in (i, hi-1): these elements were > pivot_val from loop invariant
        // 2. For k == hi-1: this position now contains the old value from position i
        
        // Case 1: elements that were > pivot_val remain > pivot_val
        assert(forall|k: int| i < k < hi - 1 ==> a[k as usize] > pivot_val);
        
        // Case 2: the element at hi-1 is now the old element from position i
        if hi - 1 > i {
            assert(a[(hi - 1) as usize] == temp);
            // temp was the old value at position i, which was <= pivot_val
            assert(temp <= pivot_val);
        }
        
        // Since a[i] == pivot_val, we have pivot_val <= all elements after i
        assert(a[i as usize] == pivot_val);
    }
    
    // Prove frame condition
    assert(forall|k: int| 0 <= k < a.len() && (k < lo || k >= hi) ==> a[k as usize] == old(a)[k as usize]);
    
    i
}

}