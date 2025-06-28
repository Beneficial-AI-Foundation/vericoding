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
        count_occurrences_range(a, v, 0, a.len() - 1) + 
        if a[a.len() - 1] == v { 1 } else { 0 }
    }
}

// Helper for counting in a range to avoid subrange issues
spec fn count_occurrences_range(a: &Vec<int>, v: int, start: int, end: int) -> nat
    requires 0 <= start <= end <= a.len()
    decreases end - start
{
    if start >= end {
        0
    } else {
        count_occurrences_range(a, v, start, end - 1) + 
        if a[end - 1] == v { 1 } else { 0 }
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
        swap_frame(a, old(a), lo as int, hi as int),
        is_permutation(a, old(a))
    decreases hi - lo
{
    if lo + 1 >= hi {
        // Base case: 0 or 1 elements, already sorted
        return;
    }
    
    // Get partition point
    let ghost old_a1 = *a;
    let p = partition(a, lo, hi);
    
    // Recursively sort left and right parts
    let ghost old_a2 = *a;
    quick_sort_aux(a, lo, p);
    
    let ghost old_a3 = *a;
    quick_sort_aux(a, p + 1, hi);
    
    // Proof that sorting preserves permutation
    proof {
        assert(is_permutation(a, &old_a3));
        assert(is_permutation(&old_a3, &old_a2));
        assert(is_permutation(&old_a2, &old_a1));
        assert(is_permutation(a, &old_a1));
    }
}

// Partition function that splits array around pivot
fn partition(a: &mut Vec<int>, lo: usize, hi: usize) -> (p: usize)
    requires 
        lo < hi,
        hi <= old(a).len()
    ensures
        lo <= p < hi,
        a.len() == old(a).len(),
        swap_frame(a, old(a), lo as int, hi as int),
        is_permutation(a, old(a))
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
            pivot_idx == hi - 1,
            a.len() == old(a).len(),
            pivot_val == old(a)[pivot_idx],
            swap_frame(a, old(a), lo as int, hi as int),
            is_permutation(a, old(a))
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
        is_sorted(a, 0, a.len() as int),
        is_permutation(a, old(a))
{
    if a.len() > 0 {
        quick_sort_aux(a, 0, a.len());
    }
}

}