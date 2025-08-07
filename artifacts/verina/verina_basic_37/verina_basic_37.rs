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
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            find_first_occurrence_precond(arr@, target),
            forall|j: int| 0 <= j < i ==> arr@[j] != target,
            arr.len() < 0x8000_0000,
        decreases arr.len() - i,
    {
        let a = arr[i];
        if a == target {
            // Found the target at index i
            assert(arr@[i as int] == target);
            assert(forall|j: int| 0 <= j < i ==> arr@[j] != target);
            assert(0 <= i < arr.len());
            return i as i32;
        } else if a > target {
            // Since array is sorted and current element > target,
            // no later elements can equal target
            assert(forall|k: int| i <= k < arr.len() ==> arr@[k] >= arr@[i as int]) by {
                let precond = find_first_occurrence_precond(arr@, target);
                assert(precond);
            }
            assert(arr@[i as int] > target);
            assert(forall|k: int| i <= k < arr.len() ==> arr@[k] > target);
            assert(forall|k: int| 0 <= k < i ==> arr@[k] != target);
            assert(forall|k: int| i <= k < arr.len() ==> arr@[k] != target);
            return -1;
        }
        i += 1;
    }
    
    // Loop completed, no element found
    assert(i == arr.len());
    assert(forall|j: int| 0 <= j < arr.len() ==> arr@[j] != target);
    -1
}

} // verus!

fn main() {}