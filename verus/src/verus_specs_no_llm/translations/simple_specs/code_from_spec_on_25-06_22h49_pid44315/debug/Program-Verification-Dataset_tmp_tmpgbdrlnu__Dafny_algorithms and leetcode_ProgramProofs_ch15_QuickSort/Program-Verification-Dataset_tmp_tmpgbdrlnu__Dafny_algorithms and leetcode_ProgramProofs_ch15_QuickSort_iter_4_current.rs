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
        SwapFrame(*a, old(a), lo, hi)
    decreases hi - lo
{
    if lo + 1 < hi {
        let ghost old_a = *a;
        let p = Partition(a, lo, hi);
        
        // After partition, we have the partition property
        assert(forall|i: int| lo <= i < p ==> a[i] <= a[p]);
        assert(forall|i: int| p < i < hi ==> a[p] <= a[i]);
        
        QuickSortAux(a, lo, p);
        QuickSortAux(a, p + 1, hi);
        
        // Prove that the entire range is now sorted
        assert(forall|i: int, j: int| lo <= i < j < hi ==> a[i] <= a[j]) by {
            // The proof follows from the recursive calls and partition property
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
        SwapFrame(*a, old(a), lo, hi)
{
    let ghost old_a = *a;
    
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
            pivot_val == old_a[pivot_idx as usize],
            a[pivot_idx as usize] == pivot_val,
            forall|k: int| lo <= k < i ==> a[k] <= pivot_val,
            forall|k: int| i <= k < j ==> a[k] > pivot_val,
            SwapFrame(*a, old_a, lo, hi - 1),
            a.len() == old_a.len()
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
    
    // Establish postconditions
    assert(lo <= i < hi);
    assert(forall|k: int| lo <= k < i ==> a[k] <= a[i]) by {
        // From loop invariant: elements before i are <= pivot_val
        // And a[i] now contains the pivot_val
    }
    assert(forall|k: int| i < k < hi ==> a[i] <= a[k]) by {
        // From loop invariant: elements between original i and j-1 are > pivot_val
        // And a[i] now contains the pivot_val, so pivot_val <= elements after i
    }
    assert(SwapFrame(*a, old_a, lo, hi)) by {
        // We only modified elements in range [lo, hi)
    }
    
    i
}

}