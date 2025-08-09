use vstd::prelude::*;

verus! {

// Precondition: array is sorted (pairwise ordered)
spec fn find_first_occurrence_precond(arr: Seq<i32>, target: i32) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
}

// Postcondition specification
spec fn find_first_occurrence_postcond(arr: Seq<i32>, target: i32, result: i32) -> bool {
    (result >= 0 ==> {
        &&& 0 <= result < arr.len()
        &&& arr[result as int] == target
        &&& forall|i: int| 0 <= i < result ==> arr[i] != target
    }) && (result == -1 ==> {
        forall|i: int| 0 <= i < arr.len() ==> arr[i] != target
    })
}

fn find_first_occurrence(arr: &Vec<i32>, target: i32) -> (result: i32)
    requires 
        find_first_occurrence_precond(arr@, target),
        arr.len() < 0x8000_0000,
    ensures
        find_first_occurrence_postcond(arr@, target, result),
{
    let mut left: usize = 0;
    let mut right: usize = arr.len();
    let mut result_idx: i32 = -1;
    
    while left < right
        invariant
            0 <= left <= right <= arr.len(),
            find_first_occurrence_precond(arr@, target),
            result_idx >= -1,
            result_idx >= 0 ==> {
                &&& 0 <= result_idx < arr.len()
                &&& arr@[result_idx as int] == target
                &&& forall|i: int| 0 <= i < result_idx ==> arr@[i] != target
            },
            result_idx == -1 ==> {
                forall|i: int| 0 <= i < left ==> arr@[i] != target
            },
            forall|i: int| right <= i < arr.len() ==> arr@[i] != target || (result_idx >= 0 && result_idx <= i),
    {
        let mid = left + (right - left) / 2;
        
        if arr[mid] == target {
            result_idx = mid as i32;
            right = mid;
        } else if arr[mid] < target {
            left = mid + 1;
        } else {
            right = mid;
        }
    }
    
    result_idx
}

} // verus!

fn main() {}