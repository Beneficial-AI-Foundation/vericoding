use vstd::prelude::*;

verus! {

fn element_wise_module(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
    // pre-conditions-start
    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] % arr2[i]) <= i32::MAX),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result@.len() == arr1@.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] % arr2[i]),
    // post-conditions-end
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 3): updated loop invariants and assertions to properly connect array length equality and preconditions */
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            arr1.len() == arr2.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (arr1[j] % arr2[j]),
        decreases arr1.len() - i
    {
        /* code modified by LLM (iteration 3): removed redundant assertions and used proper indexing consistent with preconditions */
        assert(0 <= i < arr2.len()); // follows from loop condition and arr1.len() == arr2.len()
        
        let mod_result = arr1[i] % arr2[i];
        result.push(mod_result);
        i += 1;
    }
    
    result
}

} // verus!

fn main() {}