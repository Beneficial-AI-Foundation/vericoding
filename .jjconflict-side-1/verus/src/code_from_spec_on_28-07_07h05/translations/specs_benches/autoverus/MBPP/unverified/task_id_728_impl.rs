use vstd::prelude::*;

fn main() {}

verus! {

//IMPL add_list
fn add_list(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] + arr2[i]) <= i32::MAX),
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] + arr2[i]),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 2): fixed loop invariant to include bounds for arr2 and added proper bounds checking */
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            arr1.len() == arr2.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == arr1[j] + arr2[j],
        decreases arr1.len() - i,
    {
        /* code modified by LLM (iteration 4): removed explicit assertion and let the precondition provide the overflow guarantee */
        assert(i < arr1.len());
        assert(i < arr2.len());
        assert(0 <= i < arr1.len());
        
        result.push(arr1[i] + arr2[i]);
        i += 1;
    }
    
    result
}

} // verus!