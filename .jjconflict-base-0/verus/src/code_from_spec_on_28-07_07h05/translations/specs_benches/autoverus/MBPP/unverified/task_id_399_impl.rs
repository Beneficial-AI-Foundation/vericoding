use vstd::prelude::*;

fn main() {}

verus! {

//IMPL bit_wise_xor
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
    
    /* code modified by LLM (iteration 1): strengthened invariant to include arr2 bounds and use usize type for better bounds reasoning */
    while idx < arr1.len()
        invariant
            idx <= arr1.len(),
            arr1.len() == arr2.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> result[i] == arr1[i] ^ arr2[i],
        decreases arr1.len() - idx,
    {
        /* code modified by LLM (iteration 1): added assertion to help verifier establish bounds for arr2 access */
        assert(idx < arr1.len());
        assert(arr1.len() == arr2.len());
        assert(idx < arr2.len());
        
        result.push(arr1[idx] ^ arr2[idx]);
        idx += 1;
    }
    
    result
}

} // verus!