use vstd::prelude::*;

fn main() {
    // Example usage
    let arr1 = vec![1, 2, 3];
    let arr2 = vec![3, 4, 5];
    let result = any_value_exists(&arr1, &arr2);
    println!("Any value exists: {}", result);
}

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

fn any_value_exists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
    ensures
        result == exists|k: int| 0 <= k < arr1.len() && arr2@.contains(#[trigger] arr1[k]),
{
    for i in 0..arr1.len()
        invariant
            forall|j: int| 0 <= j < i ==> !arr2@.contains(arr1[j]),
    {
        /* code modified by LLM (iteration 1): replaced arr2@.contains(arr1[i]) with contains(arr2, arr1[i]) to use executable function instead of spec function */
        if contains(arr2, arr1[i]) {
            /* code modified by LLM (iteration 1): added proof block with proper type casting from usize to int for indexing operations */
            proof {
                assert(exists|k: int| 0 <= k < arr2.len() && arr2[k] == arr1[i as int]);
                assert(arr2@.contains(arr1[i as int]));
            }
            return true;
        }
    }
    false
}

} // verus!