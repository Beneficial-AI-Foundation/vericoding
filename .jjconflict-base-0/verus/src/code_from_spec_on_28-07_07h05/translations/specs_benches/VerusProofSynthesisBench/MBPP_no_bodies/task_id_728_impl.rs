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
    
    /* code modified by LLM (iteration 1): fixed loop invariant to account for order of operations and added overflow prevention */
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            arr1.len() == arr2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == arr1[j] + arr2[j],
            forall|k: int| (0 <= k < arr1.len()) ==> (i32::MIN <= arr1[k] + arr2[k] <= i32::MAX),
        decreases arr1.len() - i
    {
        /* code modified by LLM (iteration 2): fixed type mismatch by casting i to int in assertions */
        assert(i < arr1.len());
        assert(i < arr2.len());
        assert(0 <= i as int < arr1.len());
        assert(i32::MIN <= arr1[i as int] + arr2[i as int] <= i32::MAX);
        
        let sum = arr1[i] + arr2[i];
        result.push(sum);
        
        /* code modified by LLM (iteration 1): moved increment after push to maintain invariant */
        i += 1;
        
        /* code modified by LLM (iteration 1): assertion to help prove loop invariant after increment */
        assert(forall|j: int| 0 <= j < i ==> result[j] == arr1[j] + arr2[j]);
    }
    
    result
}

} // verus!

fn main() {}