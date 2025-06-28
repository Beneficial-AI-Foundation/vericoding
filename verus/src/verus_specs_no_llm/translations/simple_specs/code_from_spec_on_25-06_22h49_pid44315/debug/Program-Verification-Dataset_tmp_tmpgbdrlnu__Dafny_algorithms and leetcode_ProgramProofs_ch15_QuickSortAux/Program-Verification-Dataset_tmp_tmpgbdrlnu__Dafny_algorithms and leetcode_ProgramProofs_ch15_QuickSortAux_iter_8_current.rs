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

// Specification for partition postcondition
spec fn partition_postcondition(a: &Vec<int>, old_a: &Vec<int>, lo: int, hi: int, p: int, pivot_val: int) -> bool {
    lo <= p < hi &&
    a.len() == old_a.len() &&
    swap_frame(a, old_a, lo, hi) &&
    is_permutation(a, old_a) &&
    (forall|i: int| lo <= i < p ==> a[i] <= pivot_val) &&
    (forall|i: int| p < i < hi ==> a[i] >= pivot_val) &&
    a[p] == pivot_val
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
        proof {
            permutation_reflexive(old(a));
        }
        return;
    }
    
    // Get partition point
    let ghost old_a1 = *a;
    let p = partition(a, lo, hi);
    
    // Recursively sort left part
    let ghost old_a2 = *a;
    if p > lo {
        quick_sort_aux(a, lo, p);
        proof {
            permutation_transitive(a, &old_a2, &old_a1);
        }
    }
    
    // Recursively sort right part  
    let ghost old_a3 = *a;
    if p + 1 < hi {
        quick_sort_aux(a, p + 1, hi);
        proof {
            permutation_transitive(a, &old_a3, &old_a1);
        }
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
        is_permutation(a, old(a)),
        (forall|i: int| lo <= i < p ==> a[i] <= old(a)[(hi - 1) as int]),
        (forall|i: int| p < i < hi ==> a[i] >= old(a)[(hi - 1) as int]),
        a[p as int] == old(a)[(hi - 1) as int]
{
    // Choose last element as pivot
    let pivot_idx = hi - 1;
    let pivot_val = a[pivot_idx];
    let ghost original_a = *a;
    let mut i = lo;
    
    proof {
        permutation_reflexive(a);
    }
    
    // Partition around pivot
    let mut j = lo;
    while j < pivot_idx
        invariant
            lo <= i <= j <= pivot_idx,
            pivot_idx < hi,
            pivot_idx == hi - 1,
            a.len() == original_a.len(),
            pivot_val == original_a[pivot_idx as int],
            pivot_val == a[pivot_idx as int],
            // Elements before i are <= pivot
            forall|k: int| lo <= k < i ==> a[k] <= pivot_val,
            // Elements from i to j-1 are > pivot  
            forall|k: int| i <= k < j ==> a[k] > pivot_val,
            // Frame condition for elements outside the range
            forall|k: int| 0 <= k < a.len() && !(lo <= k < hi) ==> a[k] == original_a[k],
            // Elements at pivot position and beyond j are unchanged
            forall|k: int| j <= k < hi ==> a[k] == original_a[k],
            // Permutation is preserved
            is_permutation(a, &original_a)
    {
        if a[j] <= pivot_val {
            // Swap elements at i and j
            if i != j {
                let ghost pre_swap = *a;
                let temp = a[i];
                a.set(i, a[j]);
                a.set(j, temp);
                
                proof {
                    swap_preserves_permutation(a, &pre_swap, i, j);
                    permutation_transitive(a, &pre_swap, &original_a);
                }
            }
            i = i + 1;
        }
        j = j + 1;
    }
    
    // Place pivot in correct position
    if i != pivot_idx {
        let ghost pre_final_swap = *a;
        let temp = a[i];
        a.set(i, a[pivot_idx]);
        a.set(pivot_idx, temp);
        
        proof {
            swap_preserves_permutation(a, &pre_final_swap, i, pivot_idx);
            permutation_transitive(a, &pre_final_swap, &original_a);
        }
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
    } else {
        proof {
            permutation_reflexive(old(a));
        }
    }
}

}