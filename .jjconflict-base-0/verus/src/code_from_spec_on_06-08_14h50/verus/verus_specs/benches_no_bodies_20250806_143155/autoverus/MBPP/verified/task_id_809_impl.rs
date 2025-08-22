use vstd::prelude::*;

fn main() {
    // Empty main function
}

verus! {

fn is_smaller(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
    requires
        arr1.len() == arr2.len(),
    ensures
        result == (forall|i: int| 0 <= i < arr1.len() ==> arr1[i] > arr2[i]),
{
    let mut idx = 0;
    while idx < arr1.len()
        invariant
            0 <= idx <= arr1.len(),
            forall|i: int| 0 <= i < idx ==> arr1[i] > arr2[i],
        /* code modified by LLM (iteration 1): Added decreases clause to ensure loop termination */
        decreases arr1.len() - idx
    {
        if arr1[idx] <= arr2[idx] {
            return false;
        }
        idx += 1;
    }
    true
}

} // verus!