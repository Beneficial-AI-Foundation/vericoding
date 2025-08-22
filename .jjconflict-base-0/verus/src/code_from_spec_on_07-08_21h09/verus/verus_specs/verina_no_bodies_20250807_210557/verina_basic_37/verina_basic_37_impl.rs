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
    
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|j: int| 0 <= j < i ==> arr@[j] != target,
        decreases arr.len() - i
    {
        if arr[i] == target {
            return i as i32;
        }
        i += 1;
    }
    
    -1
}

} // verus!

fn main() {}