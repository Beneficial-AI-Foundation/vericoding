use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

fn element_wise_division(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|m: int|
            0 <= m < arr1.len() ==> (u32::MIN <= #[trigger] arr1[m] / #[trigger] arr2[m]
                <= u32::MAX),
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] / arr2[i]),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added loop invariants to handle division by zero and bounds checking */
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            arr1.len() == arr2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == #[trigger] (arr1[j] / arr2[j]),
            forall|k: int| 0 <= k < arr2.len() ==> arr2[k] != 0,
        decreases arr1.len() - i,
    {
        /* code modified by LLM (iteration 2): fixed type mismatch by casting i to int for array indexing */
        assert(i < arr2.len());
        assert(arr2[i as int] != 0);
        let div_result = arr1[i] / arr2[i];
        result.push(div_result);
        i += 1;
    }
    
    result
}

} // verus!