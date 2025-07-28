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
    let mut idx = 0;
    
    /* code modified by LLM (iteration 1): fixed loop invariant bounds checking and added proper bounds assertions */
    while idx < arr1.len()
        invariant
            idx <= arr1.len(),
            arr1.len() == arr2.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> 0 <= i < arr1.len() && 0 <= i < arr2.len() && result[i] == arr1[i] ^ arr2[i],
        decreases arr1.len() - idx,
    {
        /* code modified by LLM (iteration 1): added bounds assertion to ensure access is safe */
        assert(idx < arr1.len());
        assert(idx < arr2.len());
        result.push(arr1[idx] ^ arr2[idx]);
        idx += 1;
    }
    
    result
}

} // verus!

fn main() {}