use vstd::prelude::*;

fn main() {
    // Example usage of element_wise_divide
    let arr1 = vec![10, 20, 30];
    let arr2 = vec![2, 4, 5];
    let result = element_wise_divide(&arr1, &arr2);
    println!("Result: {:?}", result);
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
    
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == arr1[j] / arr2[j],
    {
        let quotient = arr1[i] / arr2[i];
        result.push(quotient);
        i += 1;
    }
    
    result
}

} // verus!