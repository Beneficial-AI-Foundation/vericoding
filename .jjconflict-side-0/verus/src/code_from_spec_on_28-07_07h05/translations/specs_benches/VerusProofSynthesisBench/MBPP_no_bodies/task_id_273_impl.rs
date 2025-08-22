use vstd::prelude::*;

verus! {

//IMPL element_wise_subtract
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
    
    /* code modified by LLM (iteration 1): updated loop invariants and added arithmetic safety assertion */
    while i < arr1.len()
        invariant
            result.len() == i,
            i <= arr1.len(),
            i <= arr2.len(),
            arr1.len() == arr2.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == #[trigger] (arr1[j] - arr2[j]),
        decreases arr1.len() - i
    {
        /* code modified by LLM (iteration 1): added assertion to help verification and ensure arithmetic bounds */
        assert(0 <= i < arr1.len());
        assert(i32::MIN <= arr1[i] - arr2[i] <= i32::MAX);
        
        let diff = arr1[i] - arr2[i];
        result.push(diff);
        i = i + 1;
        
        /* code modified by LLM (iteration 1): added assertion to help prove invariant maintenance */
        assert(forall|j: int| 0 <= j < i - 1 ==> result[j] == arr1[j] - arr2[j]);
        assert(result[i - 1] == diff);
        assert(result[i - 1] == arr1[i - 1] - arr2[i - 1]);
    }
    
    result
}

} // verus!

fn main() {}