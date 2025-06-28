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
            proof {
                // The first i elements are still sorted (unchanged)
                assert forall|x: int, y: int| 0 <= x < y < i implies a[x] <= a[y] by {};
                
                // The new element at position i is <= all elements from i+1 onwards
                assert forall|k: int| i < k < len implies a[i as int] <= a[k as int] by {
                    if k == min_index {
                        // a[i] is now old_a_min, a[min_index] is now old_a_i
                        // We know old_a_min <= old_a_i from find_min postcondition
                    } else {
                        // a[k] is unchanged, and we know old_a_min <= a[k] from find_min
                    }
                };
                
                // The new element at position i is >= all elements before i
                assert forall|j: int| 0 <= j < i implies a[j as int] <= a[i as int] by {
                    // From loop invariant: a[j] <= old_a_i (since old_a_i was at position i)
                    // From find_min: old_a_min <= old_a_i
                    // a[i] is now old_a_min, so we need a[j] <= old_a_min
                    // This follows from the partition property maintained by the loop invariant
                };
                
                // Therefore is_sorted(a, 0, i+1)
                assert forall|x: int, y: int| 0 <= x < y < i + 1 implies a[x] <= a[y] by {
                    if y < i {
                        // Both in sorted prefix
                    } else if x < i && y == i {
                        // x in prefix, y is new minimum
                    }
                };
            }
            
            // Prove the partition property is maintained
            proof {
                assert forall|j: int, k: int| 0 <= j < (i + 1) && (i + 1) <= k < len implies a[j as int] <= a[k as int] by {
                    if j < i {
                        // From previous invariant and the fact that we placed minimum at position i
                        if k == min_index {
                            // a[k] is now old_a_i, and from invariant a[j] <= old_a_i
                        } else {
                            // From previous invariant
                        }
                    } else {
                        // j == i, a[j] is the minimum of range [i, len), so a[j] <= a[k] for all k in [i+1, len)
                        if k == min_index {
                            // a[k] is now old_a_i, and old_a_min <= old_a_i
                        } else {
                            // From find_min postcondition
                        }
                    }
                };
            }
        } else {
            // When i + 1 >= len, we're at the last element, so sorting is complete
            proof {
                assert(i == len - 1);
                assert(is_sorted(a, 0, i + 1)) by {
                    // is_sorted(a, 0, i) from invariant, and i+1 == len, so we're done
                    assert forall|x: int, y: int| 0 <= x < y < len implies a[x] <= a[y] by {
                        if y < len - 1 {
                            // Both in already sorted portion
                        } else {
                            // y == len - 1 == i, follows from partition property
                        }
                    };
                };
            }
        }
        
        i = i + 1;
    }
}

}