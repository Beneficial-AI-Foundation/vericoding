use vstd::prelude::*;

verus! {

fn bit_wise_xor(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        arr1.len() == arr2.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> result[i] == #[trigger] arr1[i] ^ #[trigger] arr2[i],
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut index = 0;
    
    /* code modified by LLM (iteration 1): added bounds checks for both arrays in invariants */
    while index < arr1.len()
        invariant
            index <= arr1.len(),
            arr1.len() == arr2.len(),
            result.len() == index,
            forall|i: int| 0 <= i < index && i < arr1.len() && i < arr2.len() ==> result[i] == arr1[i] ^ arr2[i],
        decreases arr1.len() - index,
    {
        result.push(arr1[index] ^ arr2[index]);
        index += 1;
    }
    
    result
}

} // verus!

fn main() {}