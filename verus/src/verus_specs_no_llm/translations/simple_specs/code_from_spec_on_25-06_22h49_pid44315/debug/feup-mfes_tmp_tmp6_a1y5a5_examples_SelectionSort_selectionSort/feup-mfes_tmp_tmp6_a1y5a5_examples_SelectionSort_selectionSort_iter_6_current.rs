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
    
    assert(forall|k: int| from <= k < to ==> a[min_index as int] <= a[k as int]);
    min_index
}

// Helper lemma to maintain sorting properties after swap
proof fn lemma_swap_maintains_sorted_prefix(a_old: &Vec<i32>, a_new: &Vec<i32>, i: usize, min_index: usize, len: usize)
    requires
        0 <= i < min_index < len <= a_old.len(),
        a_new.len() == a_old.len(),
        forall|k: int| 0 <= k < len && k != i && k != min_index ==> a_new[k] == a_old[k],
        a_new[i as int] == a_old[min_index as int],
        a_new[min_index as int] == a_old[i as int],
        is_sorted(a_old, 0, i),
        forall|j: int, k: int| 0 <= j < i && i <= k < len ==> a_old[j as int] <= a_old[k as int],
        forall|k: int| i <= k < len ==> a_old[min_index as int] <= a_old[k as int],
    ensures
        is_sorted(a_new, 0, i + 1),
        forall|j: int, k: int| 0 <= j < i + 1 && i + 1 <= k < len ==> a_new[j as int] <= a_new[k as int],
{
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
            let ghost a_old = *a;
            let min_index = find_min(a, i, len);
            
            // Perform the swap
            let temp = a[i];
            a.set(i, a[min_index]);
            a.set(min_index, temp);
            
            // Prove that the swap maintains our invariants
            if min_index != i {
                proof {
                    lemma_swap_maintains_sorted_prefix(&a_old, a, i, min_index, len);
                }
            }
        } else {
            // When i + 1 >= len, we have i == len - 1, so we're done
            assert(i == len - 1);
            assert(is_sorted(a, 0, i + 1));
        }
        
        i = i + 1;
    }
    
    assert(i == len);
    assert(is_sorted(a, 0, len));
}

}