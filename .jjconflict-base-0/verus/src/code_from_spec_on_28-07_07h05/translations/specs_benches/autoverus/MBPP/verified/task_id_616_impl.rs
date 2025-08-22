use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

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
    
    /* code modified by LLM (iteration 2): added trigger annotations to fix quantifier trigger inference error */
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            arr1.len() == arr2.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == arr1[j] % arr2[j],
            forall|j: int| 0 <= j < arr2.len() ==> arr2[j] != 0,
            forall|j: int| (0 <= j < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[j] % arr2[j]) <= i32::MAX),
        decreases arr1.len() - i
    {
        let mod_result = arr1[i] % arr2[i];
        result.push(mod_result);
        i += 1;
    }
    
    result
}

} // verus!