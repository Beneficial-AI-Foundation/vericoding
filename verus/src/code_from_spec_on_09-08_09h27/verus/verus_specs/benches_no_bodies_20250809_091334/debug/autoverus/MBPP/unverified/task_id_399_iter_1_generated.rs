use vstd::prelude::*;

fn main() {}

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
    
    while idx < arr1.len()
        invariant
            idx <= arr1.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> result[i] == arr1[i] ^ arr2[i],
    {
        let xor_val = arr1[idx] ^ arr2[idx];
        result.push(xor_val);
        idx += 1;
    }
    
    result
}

} // verus!