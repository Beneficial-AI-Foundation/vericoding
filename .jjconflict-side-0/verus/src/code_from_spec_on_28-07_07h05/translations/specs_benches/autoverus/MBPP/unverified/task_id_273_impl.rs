use vstd::prelude::*;

fn main() {}

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
    let mut i = 0usize;
    
    /* code modified by LLM (iteration 3): fixed type casting for array indexing */
    while i < arr1.len()
        invariant
            result.len() == i,
            i <= arr1.len(),
            i <= arr2.len(),
            arr1.len() == arr2.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == #[trigger] (arr1[j] - arr2[j]),
        decreases arr1.len() - i,
    {
        /* code modified by LLM (iteration 3): properly instantiate precondition for current index */
        assert(i < arr2.len());
        assert(0 <= i as int < arr1.len());
        assert(arr1[i as int] - arr2[i as int] == arr1[i] - arr2[i]);
        let diff = arr1[i] - arr2[i];
        result.push(diff);
        i += 1;
    }
    
    result
}

} // verus!