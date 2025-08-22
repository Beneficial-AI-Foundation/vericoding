use vstd::prelude::*;

fn main() {
    let arr1 = vec![10, 20, 30];
    let arr2 = vec![2, 4, 5];
    let result = element_wise_division(&arr1, &arr2);
    println!("Result: {:?}", result);
}

verus! {

fn element_wise_division(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)
    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|m: int|
            0 <= m < arr1.len() ==> (u32::MIN <= #[trigger] arr1[m] / #[trigger] arr2[m]
                <= u32::MAX),
    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] / arr2[i]),
{
    let mut result = Vec::new();
    let mut idx = 0;
    
    /* code modified by LLM (iteration 1): Added decreases clause to prove loop termination */
    while idx < arr1.len()
        invariant
            0 <= idx <= arr1.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> result[i] == arr1[i] / arr2[i],
        decreases arr1.len() - idx
    {
        let division_result = arr1[idx] / arr2[idx];
        result.push(division_result);
        idx += 1;
    }
    
    result
}

} // verus!