use vstd::prelude::*;

fn main() {}

verus! {

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
    
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    while i < arr1.len()
        invariant
            result.len() == i,
            i <= arr1.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == #[trigger] (arr1[j] + arr2[j]),
        decreases arr1.len() - i,
    {
        let sum = arr1[i] + arr2[i];
        result.push(sum);
        i += 1;
    }
    
    result
}

} // verus!