use vstd::prelude::*;

fn main() {}

verus! {

fn is_smaller(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
    requires
        arr1.len() == arr2.len(),
    ensures
        result == (forall|i: int| 0 <= i < arr1.len() ==> arr1[i] > arr2[i]),
{
    let mut index = 0;
    /* code modified by LLM (iteration 2): added bounds checks and strengthened loop invariant */
    while index < arr1.len()
        invariant
            0 <= index <= arr1.len(),
            arr1.len() == arr2.len(),
            forall|i: int| 0 <= i < index ==> arr1[i] > arr2[i],
        decreases arr1.len() - index,
    {
        /* code modified by LLM (iteration 2): added explicit bounds check for arr2 access */
        if index < arr2.len() && arr1[index] <= arr2[index] {
            return false;
        }
        index += 1;
    }
    true
}

} // verus!