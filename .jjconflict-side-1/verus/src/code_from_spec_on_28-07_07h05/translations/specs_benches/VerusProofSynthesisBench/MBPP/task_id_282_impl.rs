use vstd::prelude::*;

verus! {

fn element_wise_subtract(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        arr1.len() == arr2.len(),
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] - arr2[i]) <= i32::MAX),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] - arr2[i]),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 3): fixed invariant and overflow issues */
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            arr1.len() == arr2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j] == #[trigger] (arr1[j] - arr2[j]),
            forall|k: int| (0 <= k < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[k] - arr2[k]) <= i32::MAX),
        decreases arr1.len() - i
    {
        /* code modified by LLM (iteration 3): assert precondition for current index */
        assert(0 <= i < arr1.len());
        assert(i32::MIN <= arr1[i] - arr2[i] <= i32::MAX);
        
        let diff = arr1[i] - arr2[i];
        result.push(diff);
        i += 1;
        
        /* code modified by LLM (iteration 3): help verify invariant after push */
        assert(forall|j: int| 0 <= j < result.len() ==> result[j] == arr1[j] - arr2[j]);
    }
    
    result
}

} // verus!

fn main() {}