use vstd::prelude::*;

verus! {

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
    
    /* code modified by LLM (iteration 2): fixed assertion by using proper index type and leveraging precondition */
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            arr1.len() == arr2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> (
                j < arr1.len() && j < arr2.len() && 
                result[j] == arr1[j] * arr2[j]
            ),
        decreases arr1.len() - i
    {
        /* code modified by LLM (iteration 2): use precondition to establish overflow bounds */
        assert(0 <= i < arr1.len());
        assert(0 <= i < arr2.len());
        
        let product = arr1[i] * arr2[i];
        result.push(product);
        i += 1;
    }
    
    result
}

} // verus!

fn main() {}