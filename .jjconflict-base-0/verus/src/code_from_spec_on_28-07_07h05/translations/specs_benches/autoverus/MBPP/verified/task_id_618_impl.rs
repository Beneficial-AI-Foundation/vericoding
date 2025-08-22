use vstd::prelude::*;

fn main() {
    // TODO: Remove this comment and implement the function body
}

verus! {

fn element_wise_divide(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] / arr2[i]) <= i32::MAX),
    ensures
        result@.len() == arr1@.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] / arr2[i]),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): fixed loop invariants with proper trigger annotations */
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            arr1.len() == arr2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] arr1[j] != 0 && #[trigger] arr2[j] != 0,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == #[trigger] (arr1[j] / arr2[j]),
        decreases arr1.len() - i
    {
        /* code modified by LLM (iteration 1): fixed type mismatch by casting i to int for assertions */
        assert(i < arr1.len() && i < arr2.len());
        assert(arr2[i as int] != 0);
        
        let quotient = arr1[i] / arr2[i];
        result.push(quotient);
        i += 1;
    }
    
    result
}

} // verus!