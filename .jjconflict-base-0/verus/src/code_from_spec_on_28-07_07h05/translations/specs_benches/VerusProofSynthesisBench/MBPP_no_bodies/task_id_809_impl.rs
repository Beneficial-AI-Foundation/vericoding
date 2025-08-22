use vstd::prelude::*;

verus! {

fn is_smaller(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
    // pre-conditions-start
    requires
        arr1.len() == arr2.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == (forall|i: int| 0 <= i < arr1.len() ==> arr1[i] > arr2[i]),
    // post-conditions-end
{
    let mut idx = 0;
    while idx < arr1.len()
        invariant
            0 <= idx <= arr1.len(),
            /* code modified by LLM (iteration 1): added arr2.len() constraint to ensure safe indexing */
            arr1.len() == arr2.len(),
            forall|i: int| 0 <= i < idx ==> arr1[i] > arr2[i],
        /* code modified by LLM (iteration 1): added decreases clause to ensure loop termination */
        decreases arr1.len() - idx
    {
        /* code modified by LLM (iteration 1): added assertion to help verifier with bounds checking */
        assert(idx < arr2.len());
        if arr1[idx] <= arr2[idx] {
            return false;
        }
        idx = idx + 1;
    }
    true
}

} // verus!

fn main() {}