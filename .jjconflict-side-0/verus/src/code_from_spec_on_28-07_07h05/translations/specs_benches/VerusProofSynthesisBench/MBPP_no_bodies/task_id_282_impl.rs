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
    
    /* code modified by LLM (iteration 1): added decreases clause and fixed loop invariant to include arr2 bounds */
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            arr1.len() == arr2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == arr1[j] - arr2[j],
        decreases arr1.len() - i
    {
        /* code modified by LLM (iteration 3): removed int casts since i is already usize for array indexing */
        assert(i < arr2.len());
        assert(i32::MIN <= arr1[i as int] - arr2[i as int] <= i32::MAX);
        result.push(arr1[i] - arr2[i]);
        i += 1;
    }
    
    result
}

} // verus!

fn main() {}