use vstd::prelude::*;

verus! {

fn add_list(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        arr1.len() == arr2.len(),
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] + arr2[i]) <= i32::MAX),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] + arr2[i]),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): updated loop condition and invariant to handle both arrays properly */
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            arr1.len() == arr2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == arr1[j] + arr2[j],
        decreases arr1.len() - i
    {
        /* code modified by LLM (iteration 3): removed problematic assertion and rely on precondition directly */
        assert(i < arr1.len());  
        assert(i < arr2.len());  // This follows from arr1.len() == arr2.len()
        
        let sum = arr1[i] + arr2[i];
        result.push(sum);
        i += 1;
    }
    
    result
}

} // verus!

fn main() {}