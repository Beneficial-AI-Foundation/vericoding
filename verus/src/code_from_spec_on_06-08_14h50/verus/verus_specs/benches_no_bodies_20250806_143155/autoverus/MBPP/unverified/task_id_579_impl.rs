use vstd::prelude::*;

fn main() {}

verus! {

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    for i in 0..arr.len()
        invariant
            forall|j: int| 0 <= j < i ==> arr[j] != key,
    {
        if arr[i] == key {
            return true;
        }
    }
    false
}

fn find_dissimilar(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < arr1.len() ==> (!arr2@.contains(#[trigger] arr1[i]) ==> result@.contains(
                arr1[i],
            )),
        forall|i: int|
            0 <= i < arr2.len() ==> (!arr1@.contains(#[trigger] arr2[i]) ==> result@.contains(
                arr2[i],
            )),
        forall|i: int, j: int|
            0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
{
    let mut result = Vec::new();
    
    // Add elements from arr1 that are not in arr2
    for i in 0..arr1.len()
        invariant
            forall|k: int| 0 <= k < i ==> (!arr2@.contains(arr1[k]) ==> result@.contains(arr1[k])),
            forall|p: int, q: int| 0 <= p < q < result.len() ==> result[p] != result[q],
    {
        /* code modified by LLM (iteration 1): replaced sequence contains with helper function contains */
        if !contains(arr2, arr1[i]) && !contains(&result, arr1[i]) {
            result.push(arr1[i]);
        }
    }
    
    // Add elements from arr2 that are not in arr1
    for i in 0..arr2.len()
        invariant
            forall|k: int| 0 <= k < arr1.len() ==> (!arr2@.contains(arr1[k]) ==> result@.contains(arr1[k])),
            forall|k: int| 0 <= k < i ==> (!arr1@.contains(arr2[k]) ==> result@.contains(arr2[k])),
            forall|p: int, q: int| 0 <= p < q < result.len() ==> result[p] != result[q],
    {
        /* code modified by LLM (iteration 1): replaced sequence contains with helper function contains */
        if !contains(arr1, arr2[i]) && !contains(&result, arr2[i]) {
            result.push(arr2[i]);
        }
    }
    
    result
}

} // verus!