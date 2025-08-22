use vstd::prelude::*;

fn main() {
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
    let mut index = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while index < arr1.len()
        invariant
            result.len() == index,
            index <= arr1.len(),
            forall|i: int| 0 <= i < index ==> result[i] == arr1[i] ^ arr2[i],
        decreases arr1.len() - index
    {
        result.push(arr1[index] ^ arr2[index]);
        index += 1;
    }
    
    result
}

} // verus!