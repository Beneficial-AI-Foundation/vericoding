use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Predicate to check if array is sorted between from and to indices
spec fn is_sorted(a: &Vec<i32>, from: usize, to: usize) -> bool
{
    forall|i: int, j: int| 0 <= i < j && from <= i < j < to ==> a[i] <= a[j]
}

// Find minimum element index in range [from, to)
fn find_min(a: &Vec<i32>, from: usize, to: usize) -> (index: usize)
    requires 
        0 <= from < to <= a.len(),
    ensures 
        from <= index < to,
        forall|k: int| from <= k < to ==> a[k as int] >= a[index as int],
{
    let mut min_index = from;
    let mut i = from + 1;
    
    while i < to
        invariant
            from <= min_index < to,
            from + 1 <= i <= to,
            forall|k: int| from <= k < i ==> a[k as int] >= a[min_index as int],
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
            
            // Swap elements
            let temp = a[i];
            a.set(i, a[min_index]);
            a.set(min_index, temp);
        }
        
        i = i + 1;
    }
}

}