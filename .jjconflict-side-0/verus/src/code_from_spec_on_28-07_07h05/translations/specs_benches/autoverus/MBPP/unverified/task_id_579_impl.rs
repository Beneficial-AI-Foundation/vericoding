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

//IMPL find_dissimilar
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
            forall|k: int| 0 <= k < i && !arr2@.contains(arr1[k]) ==> result@.contains(arr1[k]),
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
            forall|k: int| 0 <= k < result.len() ==> !arr2@.contains(result[k]),
    {
        if !contains(arr2, arr1[i]) && !contains(&result, arr1[i]) {
            result.push(arr1[i]);
        }
    }
    
    // Add elements from arr2 that are not in arr1
    /* code modified by LLM (iteration 1): fixed invariants to only maintain what can actually be proven */
    for i in 0..arr2.len()
        invariant
            // Elements from arr2[0..i] that are not in arr1 are in result
            forall|k: int| 0 <= k < i && !arr1@.contains(arr2[k]) ==> result@.contains(arr2[k]),
            // No duplicates in result
            forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] != result[l],
            // All elements from arr1 that are not in arr2 are still in result (preserved from first loop)
            forall|k: int| 0 <= k < arr1.len() && !arr2@.contains(arr1[k]) ==> result@.contains(arr1[k]),
            // All elements in result are either not in arr1 or not in arr2 (or both)
            forall|k: int| 0 <= k < result.len() ==> (!arr1@.contains(result[k]) || !arr2@.contains(result[k])),
    {
        if !contains(arr1, arr2[i]) && !contains(&result, arr2[i]) {
            result.push(arr2[i]);
        }
    }
    
    result
}

} // verus!