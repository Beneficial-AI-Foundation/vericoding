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

fn difference(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < arr1.len() ==> (!(exists|j: int| 0 <= j < arr2.len() && arr2[j] == #[trigger] arr1[i]) ==> (exists|k: int| 0 <= k < result.len() && result[k] == #[trigger] arr1[i])),
        forall|i: int|
            0 <= i < arr2.len() ==> (!(exists|j: int| 0 <= j < arr1.len() && arr1[j] == #[trigger] arr2[i]) ==> (exists|k: int| 0 <= k < result.len() && result[k] == #[trigger] arr2[i])),
        forall|i: int, j: int|
            0 <= i < j < result.len() ==> #[trigger] result[i] != #[trigger] result[j],
{
    let mut result = Vec::new();
    
    // Add elements from arr1 that are not in arr2
    for i in 0..arr1.len()
        invariant
            /* code modified by LLM (iteration 2): added trigger annotations to fix quantifier trigger inference error in loop invariant */
            forall|k: int| 0 <= k < i ==> (!(exists|j: int| 0 <= j < arr2.len() && arr2[j] == #[trigger] arr1[k]) ==> (exists|m: int| 0 <= m < result.len() && result[m] == #[trigger] arr1[k])),
            forall|x: int, y: int| 0 <= x < y < result.len() ==> result[x] != result[y],
    {
        if !contains(arr2, arr1[i]) && !contains(&result, arr1[i]) {
            result.push(arr1[i]);
        }
    }
    
    // Add elements from arr2 that are not in arr1
    for i in 0..arr2.len()
        invariant
            forall|k: int| 0 <= k < arr1.len() ==> (!(exists|j: int| 0 <= j < arr2.len() && arr2[j] == arr1[k]) ==> (exists|m: int| 0 <= m < result.len() && result[m] == arr1[k])),
            /* code modified by LLM (iteration 2): added trigger annotations to fix quantifier trigger inference error in loop invariant */
            forall|k: int| 0 <= k < i ==> (!(exists|j: int| 0 <= j < arr1.len() && arr1[j] == #[trigger] arr2[k]) ==> (exists|m: int| 0 <= m < result.len() && result[m] == #[trigger] arr2[k])),
            forall|x: int, y: int| 0 <= x < y < result.len() ==> result[x] != result[y],
    {
        if !contains(arr1, arr2[i]) && !contains(&result, arr2[i]) {
            result.push(arr2[i]);
        }
    }
    
    result
}

} // verus!