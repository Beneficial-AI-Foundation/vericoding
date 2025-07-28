use vstd::prelude::*;

fn main() {}

verus! {

//IMPL element_wise_module
fn element_wise_module(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] % arr2[i]) <= i32::MAX),
    ensures
        result@.len() == arr1@.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] % arr2[i]),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added proper loop invariants and bounds checks */
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            arr1.len() == arr2.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (arr1[j] % arr2[j]),
            forall|k: int| 0 <= k < arr2.len() ==> arr2[k] != 0,
        decreases arr1.len() - i
    {
        /* code modified by LLM (iteration 2): fixed type conversion for assertion */
        assert(i < arr1.len());
        assert(arr1.len() == arr2.len());
        assert(i < arr2.len());
        assert(arr2[i as int] != 0);
        
        let mod_result = arr1[i] % arr2[i];
        result.push(mod_result);
        i += 1;
    }
    
    result
}

} // verus!