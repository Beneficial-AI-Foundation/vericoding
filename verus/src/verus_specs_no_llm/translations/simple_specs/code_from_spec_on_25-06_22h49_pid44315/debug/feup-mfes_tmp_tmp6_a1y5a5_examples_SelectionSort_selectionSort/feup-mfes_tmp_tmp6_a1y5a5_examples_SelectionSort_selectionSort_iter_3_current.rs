use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Predicate to check if array is sorted between from and to indices
spec fn is_sorted(a: &Vec<i32>, from: usize, to: usize) -> bool
{
    forall|i: int, j: int| from <= i < j < to ==> a[i as int] <= a[j as int]
}

// Find minimum element index in range [from, to)
fn find_min(a: &Vec<i32>, from: usize, to: usize) -> (index: usize)
    requires 
        0 <= from < to <= a.len(),
    ensures 
        from <= index < to,
        forall|k: int| from <= k < to ==> a[index as int] <= a[k as int],
{
    let mut min_index = from;
    let mut i = from + 1;
    
    while i < to
        invariant
            from <= min_index < to,
            from + 1 <= i <= to,
            forall|k: int| from <= k < i ==> a[min_index as int] <= a[k as int],
    {
        if a[i] < a[min_index] {
            min_index = i;
        }
        i = i + 1;
    }
    
    min_index
}

// Selection sort implementation
fn selection_sort(a: &mut Vec<i32>)
    ensures 
        is_sorted(a, 0, a.len()),
        a.len() == old(a).len(),
{
    let mut i = 0;
    let len = a.len();
    
    while i < len
        invariant
            0 <= i <= len,
            a.len() == len,
            is_sorted(a, 0, i),
            forall|j: int, k: int| 0 <= j < i && i <= k < len ==> a[j as int] <= a[k as int],
    {
        if i + 1 < len {
            let min_index = find_min(a, i, len);
            
            // Store old values for the swap
            let old_a_i = a[i];
            let old_a_min = a[min_index];
            
            // Perform the swap
            a.set(i, old_a_min);
            a.set(min_index, old_a_i);
            
            // Prove that the invariant is maintained after the swap
            assert(is_sorted(a, 0, i + 1)) by {
                // The first i elements are still sorted
                assert(is_sorted(a, 0, i));
                // The new element at position i is <= all elements from i+1 onwards
                assert(forall|k: int| i < k < len ==> a[i as int] <= a[k as int]);
                // The new element at position i is >= all elements before i
                assert(forall|j: int| 0 <= j < i ==> a[j as int] <= a[i as int]);
            };
            
            assert(forall|j: int, k: int| 0 <= j < (i + 1) && (i + 1) <= k < len ==> a[j as int] <= a[k as int]) by {
                // Elements 0..i+1 are <= elements i+1..len
                // This follows from the fact that a[i] was the minimum of elements i..len
                // and elements 0..i were already <= elements i..len
            };
        } else {
            // When i + 1 >= len, we're at the last element, so sorting is complete
            assert(i == len - 1);
            assert(is_sorted(a, 0, i + 1));
        }
        
        i = i + 1;
    }
}

}