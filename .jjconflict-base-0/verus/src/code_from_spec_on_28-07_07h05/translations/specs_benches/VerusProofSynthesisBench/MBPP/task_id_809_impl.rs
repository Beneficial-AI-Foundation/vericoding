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
    let mut index = 0;
    
    /* code modified by LLM (iteration 2): added invariant to establish arr2 bounds and fixed loop condition bounds check */
    while index < arr1.len()
        invariant
            0 <= index <= arr1.len(),
            arr1.len() == arr2.len(),
            forall|i: int| 0 <= i < index ==> arr1[i] > arr2[i],
        decreases arr1.len() - index,
    {
        /* code modified by LLM (iteration 2): added assertion to help verifier understand bounds */
        assert(index < arr2.len());
        if arr1[index] <= arr2[index] {
            return false;
        }
        index += 1;
    }
    
    true
}

} // verus!

fn main() {}