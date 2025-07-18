use vstd::prelude::*;

verus! {

fn is_smaller(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
    requires
        arr1.len() == arr2.len(),
    ensures
        result == (forall|i: int| 0 <= i < arr1.len() ==> arr1[i] > arr2[i]),
{
    /* code modified by LLM (iteration 3): Fixed array indexing by ensuring bounds are properly checked for both arrays */
    let mut index = 0;
    while index < arr1.len()
        invariant
            0 <= index <= arr1.len(),
            arr1.len() == arr2.len(),
            forall|i: int| 0 <= i < index ==> arr1[i] > arr2[i],
        decreases arr1.len() - index,
    {
        /* code modified by LLM (iteration 3): Added bounds check assertion to ensure safe array access */
        assert(index < arr1.len());
        assert(index < arr2.len()); // This follows from arr1.len() == arr2.len()
        
        if arr1[index] <= arr2[index] {
            return false;
        }
        index += 1;
    }
    return true;
}

} // verus!

fn main() {}