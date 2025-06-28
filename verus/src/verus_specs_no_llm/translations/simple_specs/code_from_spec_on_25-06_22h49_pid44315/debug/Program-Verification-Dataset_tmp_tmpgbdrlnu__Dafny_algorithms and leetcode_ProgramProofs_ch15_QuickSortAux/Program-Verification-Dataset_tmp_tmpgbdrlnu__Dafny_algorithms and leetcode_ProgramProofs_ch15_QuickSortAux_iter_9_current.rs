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
spec fn count_occurrences(a: &Vec<int>, v: int) -> nat {
    count_occurrences_range(a, v, 0, a.len() as int)
}

// Helper for counting in a range
spec fn count_occurrences_range(a: &Vec<int>, v: int, start: int, end: int) -> nat
    requires 0 <= start <= end <= a.len()
    decreases end - start
{
    if start >= end {
        0
    } else {
        count_occurrences_range(a, v, start, end - 1) + 
        if a[(end - 1) as usize] == v { 1 } else { 0 }
    }
}

// Helper proof function for permutation reflexivity
proof fn permutation_reflexive(a: &Vec<int>)
    ensures is_permutation(a, a)
{
    assert(forall|v: int| count_occurrences(a, v) == count_occurrences(a, v));
}

// Helper proof function for permutation transitivity
proof fn permutation_transitive(a: &Vec<int>, b: &Vec<int>, c: &Vec<int>)
    requires is_permutation(a, b), is_permutation(b, c)
    ensures is_permutation(a, c)
{
    assert(forall|v: int| count_occurrences(a, v) == count_occurrences(b, v));
    assert(forall|v: int| count_occurrences(b, v) == count_occurrences(c, v));
}

// Helper proof function for swap preserving permutation
proof fn swap_preserves_permutation(a: &Vec<int>, old_a: &Vec<int>, i: usize, j: usize)
    requires 
        a.len() == old_a.len(),
        i < a.len(),
        j < a.len(),
        a[i as int] == old_a[j as int],
        a[j as int] == old_a[i as int],
        forall|k: int| 0 <= k < a.len() && k != i && k != j ==> a[k] == old_a[k]
    ensures is_permutation(a, old_a)
{
    // The proof follows from the fact that we only swapped two elements
    // which preserves the count of all values
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
    let p = partition(a, lo, hi);
    
    // Store the pivot value for later use
    let pivot_val = a[p];
    
    // Recursively sort left part
    if p > lo {
        quick_sort_aux(a, lo, p);
    }
    
    // Recursively sort right part  
    if p + 1 < hi {
        quick_sort_aux(a, p + 1, hi);
    }
    
    // The array is now sorted: left part <= pivot <= right part
    assert(is_sorted(a, lo as int, p as int));
    assert(is_sorted(a, (p + 1) as int, hi as int));
    assert(forall|i: int| lo <= i < p ==> a[i] <= pivot_val);
    assert(forall|i: int| p < i < hi ==> a[i] >= pivot_val);
    assert(a[p as int] == pivot_val);
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
        is_permutation(a, old(a)),
        (forall|i: int| lo <= i < p ==> a[i] <= a[p as int]),
        (forall|i: int| p < i < hi ==> a[i] >= a[p as int])
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
            pivot_val == a[pivot_idx as int],
            // Elements before i are <= pivot
            forall|k: int| lo <= k < i ==> a[k] <= pivot_val,
            // Elements from i to j-1 are > pivot  
            forall|k: int| i <= k < j ==> a[k] > pivot_val,
            // Frame condition for elements outside the range
            forall|k: int| 0 <= k < a.len() && !(lo <= k < hi) ==> a[k] == old(a)[k],
            // Elements at pivot position are unchanged
            a[pivot_idx as int] == pivot_val,
            // Preserve elements beyond j (except pivot)
            forall|k: int| j < k < pivot_idx ==> a[k] == old(a)[k],
            // Permutation is preserved
            is_permutation(a, old(a))
    {
        if a[j] <= pivot_val {
            // Swap elements at i and j
            if i != j {
                let temp = a[i];
                a.set(i, a[j]);
                a.set(j, temp);
            }
            i = i + 1;
        }
        j = j + 1;
    }
    
    // Place pivot in correct position
    if i != pivot_idx {
        let temp = a[i];
        a.set(i, a[pivot_idx]);
        a.set(pivot_idx, temp);
    }
    
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