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
    
    /* code modified by LLM (iteration 2): fixed loop condition and invariants to ensure bounds checking and division by zero safety */
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            i <= arr2.len(),
            arr1.len() == arr2.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (arr1[j] % arr2[j]),
            forall|j: int| 0 <= j < arr2.len() ==> arr2[j] != 0,
        decreases arr1.len() - i
    {
        /* code modified by LLM (iteration 2): added bounds and division by zero checks with proper type casting */
        assert(i < arr1.len());
        assert(i < arr2.len());
        assert(arr2[i as int] != 0);
        let mod_result = arr1[i] % arr2[i];
        result.push(mod_result);
        i += 1;
    }
    
    result
}

} // verus!

fn main() {}