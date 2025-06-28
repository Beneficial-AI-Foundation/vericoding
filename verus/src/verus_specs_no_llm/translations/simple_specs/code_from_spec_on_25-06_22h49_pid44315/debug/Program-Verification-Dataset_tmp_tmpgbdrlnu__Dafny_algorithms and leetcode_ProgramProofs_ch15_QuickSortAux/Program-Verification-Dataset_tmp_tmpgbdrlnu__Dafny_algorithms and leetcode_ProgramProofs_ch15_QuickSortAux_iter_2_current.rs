use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Predicate to check if array is sorted between indices
spec fn is_sorted(a: &Vec<int>, start: int, end: int) -> bool {
    forall|i: int, j: int| start <= i < j < end ==> a[i] <= a[j]
}

// Predicate to check if only elements between lo and hi were modified
spec fn swap_frame(a: &Vec<int>, old_a: &Vec<int>, lo: int, hi: int) -> bool {
    a.len() == old_a.len() &&
    forall|i: int| 0 <= i < a.len() && !(lo <= i < hi) ==> a[i] == old_a[i]
}

// Predicate to check if array contains same elements (permutation)
spec fn is_permutation(a: &Vec<int>, b: &Vec<int>) -> bool {
    a.len() == b.len() &&
    forall|v: int| count_occurrences(a, v) == count_occurrences(b, v)
}

// Helper function to count occurrences of a value
spec fn count_occurrences(a: &Vec<int>, v: int) -> nat 
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        count_occurrences(&a.subrange(0, a.len() - 1), v) + 
        if a[a.len() - 1] == v { 1 } else { 0 }
    }
}

// QuickSort auxiliary function
fn quick_sort_aux(a: &mut Vec<int>, lo: usize, hi: usize)
    requires 
        lo <= hi,
        hi <= old(a).len()
    ensures
        a.len() == old(a).len(),
        is_sorted(a, lo as int, hi as int),
        swap_frame(a, old(a), lo as int, hi as int)
    decreases hi - lo
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
        hi <= old(a).len()
    ensures
        lo <= p < hi,
        a.len() == old(a).len(),
        swap_frame(a, old(a), lo as int, hi as int)
{
    // Choose last element as pivot
    let pivot_idx = hi - 1;
    let pivot_val = a[pivot_idx];
    let mut i = lo;
    
    // Partition around pivot
    let mut j = lo;
    while j < pivot_idx
        invariant
            lo <= i <= j <= pivot_idx,
            pivot_idx < hi,
            a.len() == old(a).len()
    {
        if a[j] < pivot_val {
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
        is_sorted(a, 0, a.len() as int)
{
    if a.len() > 0 {
        quick_sort_aux(a, 0, a.len());
    }
}

}