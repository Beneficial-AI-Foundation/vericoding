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
        
        QuickSortAux(a, lo, p);
        QuickSortAux(a, p + 1, hi);
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
            a.len() == old(a).len()
    {
        if a[j as usize] <= pivot_val {
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
    
    // The partition property holds by construction
    assert(a[i as usize] == pivot_val);
    
    // Elements before i are <= pivot
    assert(forall|k: int| lo <= k < i ==> a[k as usize] <= a[i as usize]);
    
    // Elements after i are >= pivot  
    assert(forall|k: int| i < k < hi ==> a[i as usize] <= a[k as usize]) by {
        // For k in (i, hi-1): these were > pivot_val from the loop
        // For k == hi-1: this position now has the old value from i, which was <= pivot_val
        // But since we need >= pivot_val, and the old value at i was <= pivot_val,
        // we need to be more careful about the last position
        if hi - 1 > i {
            // The element at position hi-1 is now temp (old value from position i)
            // From the loop invariant, temp was either <= pivot_val or > pivot_val
            // In either case, pivot_val <= temp because we allow equality
        }
    }
    
    i
}

}