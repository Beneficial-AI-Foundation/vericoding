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
        if arr2@.contains(arr1[i]) {
            return true;
        }
    }
    false
}

} // verus!