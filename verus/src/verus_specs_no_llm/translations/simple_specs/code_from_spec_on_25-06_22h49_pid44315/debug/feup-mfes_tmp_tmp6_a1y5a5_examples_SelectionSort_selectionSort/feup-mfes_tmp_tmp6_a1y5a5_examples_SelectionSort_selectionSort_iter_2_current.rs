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
            
            // Swap elements with proof annotations
            let old_a_i = a[i];
            let old_a_min = a[min_index];
            
            a.set(i, old_a_min);
            a.set(min_index, old_a_i);
            
            // Help the verifier understand the sorting property is preserved
            assert forall|j: int, k: int| 0 <= j < i && i < k < len implies a[j as int] <= a[k as int] by {
                // The elements before i are still <= elements after i
                // because we placed the minimum at position i
            };
            
            assert forall|j: int| 0 <= j < i implies a[j as int] <= a[i as int] by {
                // The new element at position i is the minimum of the remaining elements
            };
        }
        
        i = i + 1;
    }
}

}