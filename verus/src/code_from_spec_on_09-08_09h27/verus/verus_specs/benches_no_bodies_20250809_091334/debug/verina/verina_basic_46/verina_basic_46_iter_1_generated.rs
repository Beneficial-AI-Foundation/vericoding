use vstd::prelude::*;

verus! {

// Precondition: array is sorted (non-decreasing)
spec fn last_position_precond(arr: &Vec<i32>, elem: i32) -> bool {
    // List.Pairwise (· ≤ ·) arr.toList
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
}

// Check if all elements in slice are not equal to elem
spec fn all_not_equal(arr: &Vec<i32>, start: int, end: int, elem: i32) -> bool {
    forall|k: int| start <= k < end ==> arr[k] != elem
}

// Postcondition specification
spec fn last_position_postcond(arr: &Vec<i32>, elem: i32, result: i32) -> bool {
    (result >= 0 ==> 
        result < arr.len() &&
        arr[result as int] == elem &&
        all_not_equal(arr, result as int + 1, arr.len() as int, elem)
    ) &&
    (result == -1 ==> all_not_equal(arr, 0, arr.len() as int, elem))
}

fn last_position(arr: &Vec<i32>, elem: i32) -> (result: i32)
    requires 
        last_position_precond(arr, elem),
        arr.len() < 0x8000_0000, // ensure i32 conversion is safe
    ensures 
        last_position_postcond(arr, elem, result)
{
    if arr.len() == 0 {
        return -1;
    }
    
    let mut left: usize = 0;
    let mut right: usize = arr.len() - 1;
    let mut found_pos: i32 = -1;
    
    while left <= right
        invariant
            left <= arr.len(),
            right < arr.len(),
            left <= right + 1,
            last_position_precond(arr, elem),
            // If found_pos >= 0, it's a valid position with the element
            found_pos >= 0 ==> found_pos < arr.len() && arr[found_pos as int] == elem,
            // All elements before left don't equal elem OR are not the last occurrence
            forall|k: int| 0 <= k < left ==> arr[k] != elem || (exists|j: int| k < j < arr.len() && arr[j] == elem),
            // All elements after right don't equal elem
            forall|k: int| right < k < arr.len() ==> arr[k] != elem,
            // If we have a found_pos, no element after it equals elem
            found_pos >= 0 ==> all_not_equal(arr, found_pos as int + 1, arr.len() as int, elem),
    {
        let mid = left + (right - left) / 2;
        
        if arr[mid] == elem {
            found_pos = mid as i32;
            if mid == right {
                break;
            }
            left = mid + 1;
        } else if arr[mid] < elem {
            if mid == right {
                break;
            }
            left = mid + 1;
        } else {
            if mid == 0 {
                break;
            }
            right = mid - 1;
        }
    }
    
    found_pos
}

fn main() {}

} // verus!