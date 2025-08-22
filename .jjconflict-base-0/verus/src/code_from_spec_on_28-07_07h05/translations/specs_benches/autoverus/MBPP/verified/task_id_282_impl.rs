use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

fn element_wise_subtract(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] - arr2[i]) <= i32::MAX),
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] - arr2[i]),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 2): strengthened loop invariant with trigger annotation for quantifier */
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            arr1.len() == arr2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == arr1[j] - arr2[j],
            forall|j: int| 0 <= j < arr1.len() ==> (i32::MIN <= #[trigger] (arr1[j] - arr2[j]) <= i32::MAX),
        decreases arr1.len() - i,
    {
        /* code modified by LLM (iteration 1): arithmetic operation is now proven safe by invariant and i < arr1.len() condition */
        result.push(arr1[i] - arr2[i]);
        i += 1;
    }
    
    result
}

} // verus!