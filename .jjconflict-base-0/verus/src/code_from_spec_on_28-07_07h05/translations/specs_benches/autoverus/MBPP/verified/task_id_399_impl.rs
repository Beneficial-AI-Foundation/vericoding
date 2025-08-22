use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

fn bit_wise_xor(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires
        arr1.len() == arr2.len(),
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> result[i] == #[trigger] arr1[i] ^ #[trigger] arr2[i],
{
    let mut result = Vec::new();
    let mut idx = 0;
    
    /* code modified by LLM (iteration 1): added bounds checks in invariant and improved loop structure */
    while idx < arr1.len()
        invariant
            result.len() == idx,
            idx <= arr1.len(),
            arr1.len() == arr2.len(),
            forall|i: int| 0 <= i < idx && i < arr1.len() && i < arr2.len() ==> result[i] == arr1[i] ^ arr2[i],
        decreases arr1.len() - idx,
    {
        /* code modified by LLM (iteration 1): added explicit bounds assertion */
        assert(idx < arr1.len());
        assert(idx < arr2.len());
        result.push(arr1[idx] ^ arr2[idx]);
        idx += 1;
    }
    
    result
}

} // verus!