use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Predicate to check if array is sorted between from and to indices
spec fn is_sorted(a: &Vec<i32>, from: usize, to: usize) -> bool
{
    forall|i: usize, j: usize| from <= i < j < to ==> a[i as int] <= a[j as int]
}

// Find minimum element index in range [from, to)
fn find_min(a: &Vec<i32>, from: usize, to: usize) -> (index: usize)
    requires 
        0 <= from < to <= a.len(),
    ensures 
        from <= index < to,
        forall|k: usize| from <= k < to ==> a[index as int] <= a[k as int],
{
    let mut min_index = from;
    let mut i = from + 1;
    
    while i < to
        invariant
            from <= min_index < to,
            from + 1 <= i <= to,
            forall|k: usize| from <= k < i ==> a[min_index as int] <= a[k as int],
        decreases to - i,
    {
        if a[i] < a[min_index] {
            min_index = i;
        }
        i = i + 1;
    }
    
    min_index
}

// Helper lemma to maintain sorting properties after swap
proof fn lemma_swap_maintains_sorted_prefix(a_old: Vec<i32>, a_new: &Vec<i32>, i: usize, min_index: usize, len: usize)
    requires
        0 <= i < min_index < len <= a_old.len(),
        a_new.len() == a_old.len(),
        forall|k: usize| 0 <= k < len && k != i && k != min_index ==> a_new[k as int] == a_old[k as int],
        a_new[i as int] == a_old[min_index as int],
        a_new[min_index as int] == a_old[i as int],
        is_sorted(&a_old, 0, i),
        forall|j: usize, k: usize| 0 <= j < i && i <= k < len ==> a_old[j as int] <= a_old[k as int],
        forall|k: usize| i <= k < len ==> a_old[min_index as int] <= a_old[k as int],
    ensures
        is_sorted(a_new, 0, i + 1),
        forall|j: usize, k: usize| 0 <= j < i + 1 && i + 1 <= k < len ==> a_new[j as int] <= a_new[k as int],
{
    // First prove is_sorted(a_new, 0, i + 1)
    assert forall|x: usize, y: usize| 0 <= x < y < i + 1 implies a_new[x as int] <= a_new[y as int] by {
        if x < i && y < i {
            // Both in sorted prefix, unchanged by swap
            assert(a_new[x as int] == a_old[x as int] && a_new[y as int] == a_old[y as int]);
        } else if x < i && y == i {
            // x in sorted prefix, y is the new element at position i
            assert(a_new[y as int] == a_old[min_index as int]);
            assert(a_new[x as int] == a_old[x as int]);
        }
    };
    
    // Prove the cross-section property for the new array
    assert forall|j: usize, k: usize| 0 <= j < i + 1 && i + 1 <= k < len implies a_new[j as int] <= a_new[k as int] by {
        if j < i {
            assert(a_new[j as int] == a_old[j as int]);
            if k == min_index {
                assert(a_new[k as int] == a_old[i as int]);
            } else {
                assert(a_new[k as int] == a_old[k as int]);
            }
        } else if j == i {
            assert(a_new[j as int] == a_old[min_index as int]);
            if k == min_index {
                assert(a_new[k as int] == a_old[i as int]);
            } else {
                assert(a_new[k as int] == a_old[k as int]);
            }
        }
    };
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
            forall|j: usize, k: usize| 0 <= j < i && i <= k < len ==> a[j as int] <= a[k as int],
        decreases len - i,
    {
        if i + 1 < len {
            let ghost a_old = *a;
            let min_index = find_min(a, i, len);
            
            // Swap elements at positions i and min_index
            let temp = a[i];
            a.set(i, a[min_index]);
            a.set(min_index, temp);
            
            // Prove that the swap maintains our invariants
            if min_index != i {
                proof {
                    lemma_swap_maintains_sorted_prefix(a_old, a, i, min_index, len);
                }
            } else {
                // If min_index == i, no actual swap occurred, properties trivially maintained
                assert(is_sorted(a, 0, i + 1));
                assert(forall|j: usize, k: usize| 0 <= j < i + 1 && i + 1 <= k < len ==> a[j as int] <= a[k as int]);
            }
        } else {
            // When i + 1 >= len, we have i == len - 1 (since i < len from loop condition)
            assert(i == len - 1);
            // Prove that adding the last element maintains sorting
            assert forall|x: usize, y: usize| 0 <= x < y < len implies a[x as int] <= a[y as int] by {
                if y < len - 1 {
                    // Both in the already sorted prefix
                } else if y == len - 1 && x < len - 1 {
                    // y is the last element, x is before it - use cross-section property
                }
            }
        }
        
        i = i + 1;
    }
}

}