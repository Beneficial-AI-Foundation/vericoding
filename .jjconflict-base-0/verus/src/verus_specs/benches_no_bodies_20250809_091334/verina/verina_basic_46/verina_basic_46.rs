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
    return 0;  // TODO: Remove this line and implement the function body
}

fn main() {}

} // verus!