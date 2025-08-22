use vstd::prelude::*;

verus! {

//IMPL element_wise_multiplication
fn element_wise_multiplication(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        arr1.len() == arr2.len(),
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] * arr2[i]) <= i32::MAX),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] * arr2[i]),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < arr1.len()
        invariant
            result.len() == i,
            i <= arr1.len(),
            arr1.len() == arr2.len(),
            forall|j: int| 0 <= j < i ==> result[j] == arr1[j] * arr2[j],
        decreases arr1.len() - i,
    {
        /* code modified by LLM (iteration 1): properly instantiate precondition by asserting bounds and triggering quantifier */
        assert(0 <= i as int < arr1.len() as int);
        assert(arr1[i as int] * arr2[i as int] == arr1[i as int] * arr2[i as int]); // trigger the quantifier
        
        let product = arr1[i] * arr2[i];
        result.push(product);
        i += 1;
    }
    
    result
}

} // verus!

fn main() {}