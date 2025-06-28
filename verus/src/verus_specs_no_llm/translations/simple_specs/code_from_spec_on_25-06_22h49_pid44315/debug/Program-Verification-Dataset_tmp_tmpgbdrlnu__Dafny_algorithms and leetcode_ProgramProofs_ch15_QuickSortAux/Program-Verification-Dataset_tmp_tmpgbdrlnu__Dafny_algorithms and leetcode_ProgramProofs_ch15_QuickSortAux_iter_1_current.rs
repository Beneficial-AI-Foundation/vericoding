use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Predicate to check if array is split correctly at point n
spec fn split_point(a: &Vec<int>, n: int) -> bool {
    0 <= n <= a.len() &&
    forall|i: int, j: int| 0 <= i < n <= j < a.len() ==> a[i] <= a[j]
}

// Predicate to check if only elements between lo and hi were modified
spec fn swap_frame(a: &Vec<int>, old_a: &Vec<int>, lo: int, hi: int) -> bool {
    a.len() == old_a.len() &&
    forall|i: int| 0 <= i < a.len() && !(lo <= i < hi) ==> a[i] == old_a[i]
}

// QuickSort auxiliary function
fn quick_sort_aux(a: &mut Vec<int>, lo: usize, hi: usize)
    requires 
        lo <= hi,
        hi <= old(a).len(),
        split_point(old(a), lo as int),
        split_point(old(a), hi as int)
    ensures
        a.len() == old(a).len(),
        forall|i: int, j: int| lo <= i < j < hi ==> a[i] <= a[j],
        swap_frame(a, old(a), lo as int, hi as int),
        split_point(a, lo as int),
        split_point(a, hi as int)
{
    if lo + 1 >= hi {
        // Base case: 0 or 1 elements, already sorted
        return;
    }
    
    // Get partition point
    let p = partition(a, lo, hi);
    
    // Recursively sort left and right parts
    quick_sort_aux(a, lo, p);
    quick_sort_aux(a, p + 1, hi);
}

// Partition function that splits array around pivot
fn partition(a: &mut Vec<int>, lo: usize, hi: usize) -> (p: usize)
    requires 
        lo < hi,
        hi <= old(a).len(),
        split_point(old(a), lo as int),
        split_point(old(a), hi as int)
    ensures
        lo <= p < hi,
        forall|i: int| lo <= i < p ==> a[i] < a[p as int],
        forall|i: int| p < i < hi ==> a[p as int] <= a[i],
        split_point(a, lo as int),
        split_point(a, hi as int),
        swap_frame(a, old(a), lo as int, hi as int)
{
    // Choose last element as pivot
    let pivot_idx = hi - 1;
    let mut i = lo;
    
    // Partition around pivot
    let mut j = lo;
    while j < pivot_idx
        invariant
            lo <= i <= j <= pivot_idx,
            pivot_idx < hi,
            forall|k: int| lo <= k < i ==> a[k] < a[pivot_idx as int],
            forall|k: int| i <= k < j ==> a[k] >= a[pivot_idx as int]
    {
        if a[j] < a[pivot_idx] {
            // Swap elements at i and j
            let temp = a[i];
            a.set(i, a[j]);
            a.set(j, temp);
            i = i + 1;
        }
        j = j + 1;
    }
    
    // Place pivot in correct position
    let temp = a[i];
    a.set(i, a[pivot_idx]);
    a.set(pivot_idx, temp);
    
    i
}

// Public QuickSort interface
pub fn quick_sort(a: &mut Vec<int>)
    ensures
        a.len() == old(a).len(),
        forall|i: int, j: int| 0 <= i < j < a.len() ==> a[i] <= a[j]
{
    if a.len() > 0 {
        quick_sort_aux(a, 0, a.len());
    }
}

}