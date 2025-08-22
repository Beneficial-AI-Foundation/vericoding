use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

//IMPL element_wise_multiplication
fn element_wise_multiplication(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires
        /* code modified by LLM (iteration 1): fixed typo in requires clause */
        arr1.len() == arr2.len(),
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] * arr2[i]) <= i32::MAX),
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] * arr2[i]),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 3): added trigger annotation to overflow check quantifier */
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            arr1.len() == arr2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == arr1[j] * arr2[j],
            forall|j: int| 0 <= j < arr1.len() ==> (i32::MIN <= #[trigger] (arr1[j] * arr2[j]) <= i32::MAX),
        decreases arr1.len() - i,
    {
        /* code modified by LLM (iteration 2): fixed type casting for array indexing in assertions */
        assert(i < arr1.len());
        assert(i < arr2.len());
        assert(i32::MIN <= arr1[i as int] * arr2[i as int] <= i32::MAX);
        
        result.push(arr1[i] * arr2[i]);
        i += 1;
    }
    
    result
}

} // verus!