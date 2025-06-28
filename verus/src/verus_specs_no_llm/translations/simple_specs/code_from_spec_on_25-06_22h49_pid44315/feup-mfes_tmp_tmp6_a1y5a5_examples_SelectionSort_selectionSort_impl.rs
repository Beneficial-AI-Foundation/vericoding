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

// Helper lemma to prove sorting properties after swap
proof fn lemma_swap_maintains_sorting(a_old: Vec<i32>, a_new: &Vec<i32>, i: usize, min_index: usize, len: usize)
    requires
        0 <= i < len <= a_old.len(),
        i <= min_index < len,
        a_new.len() == a_old.len(),
        // Swap occurred
        a_new[i as int] == a_old[min_index as int],
        a_new[min_index as int] == a_old[i as int],
        // Other elements unchanged
        forall|k: usize| 0 <= k < len && k != i && k != min_index ==> a_new[k as int] == a_old[k as int],
        // Previous invariants
        is_sorted(&a_old, 0, i),
        forall|j: usize, k: usize| 0 <= j < i && i <= k < len ==> a_old[j as int] <= a_old[k as int],
        forall|k: usize| i <= k < len ==> a_old[min_index as int] <= a_old[k as int],
    ensures
        is_sorted(a_new, 0, i + 1),
        forall|j: usize, k: usize| 0 <= j < i + 1 && i + 1 <= k < len ==> a_new[j as int] <= a_new[k as int],
{
    // Prove is_sorted(a_new, 0, i + 1)
    assert forall|x: usize, y: usize| 0 <= x < y < i + 1 implies a_new[x as int] <= a_new[y as int] by {
        if x < i && y < i {
            // Both in the original sorted prefix
            assert(a_new[x as int] == a_old[x as int]);
            assert(a_new[y as int] == a_old[y as int]);
        } else if x < i && y == i {
            // x in sorted prefix, y is the new minimum at position i
            assert(a_new[x as int] == a_old[x as int]);
            assert(a_new[y as int] == a_old[min_index as int]);
            // From cross-section property: a_old[x] <= a_old[min_index]
        }
    };
    
    // Prove cross-section property
    assert forall|j: usize, k: usize| 0 <= j < i + 1 && i + 1 <= k < len implies a_new[j as int] <= a_new[k as int] by {
        if j < i {
            assert(a_new[j as int] == a_old[j as int]);
            if k == min_index {
                assert(a_new[k as int] == a_old[i as int]);
                // From cross-section property: a_old[j] <= a_old[i]
            } else {
                assert(a_new[k as int] == a_old[k as int]);
                // From cross-section property: a_old[j] <= a_old[k]
            }
        } else if j == i {
            assert(a_new[j as int] == a_old[min_index as int]);
            if k == min_index {
                assert(a_new[k as int] == a_old[i as int]);
                // a_old[min_index] <= a_old[i] from min property
            } else {
                assert(a_new[k as int] == a_old[k as int]);
                // a_old[min_index] <= a_old[k] from min property
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
            // Standard case: find minimum and swap
            let ghost a_old = *a;
            let min_index = find_min(a, i, len);
            
            // Swap elements at positions i and min_index
            let temp = a[i];
            a.set(i, a[min_index]);
            a.set(min_index, temp);
            
            // Apply lemma to prove invariants are maintained
            proof {
                lemma_swap_maintains_sorting(a_old, a, i, min_index, len);
            }
        } else {
            // Last element case: i == len - 1
            assert(i == len - 1);
            // The array is already sorted up to i, and there's only one element left
            // So the entire array is sorted
            assert forall|x: usize, y: usize| 0 <= x < y < len implies a[x as int] <= a[y as int] by {
                if y < len - 1 {
                    // Both x and y are in the sorted prefix [0, i)
                } else {
                    // y == len - 1, x < len - 1, so x < i and i <= y
                    // Use cross-section property
                }
            }
        }
        
        i = i + 1;
    }
}

}