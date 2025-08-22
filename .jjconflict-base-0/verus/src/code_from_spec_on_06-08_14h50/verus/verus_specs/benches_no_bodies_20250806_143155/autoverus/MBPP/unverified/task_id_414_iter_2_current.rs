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

fn any_value_exists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
    ensures
        result == exists|k: int| 0 <= k < arr1.len() && arr2@.contains(#[trigger] arr1[k]),
{
    /* code modified by LLM (iteration 1): replaced arr2@.contains() with contains() function call and added proof block */
    for i in 0..arr1.len()
        invariant
            forall|k: int| 0 <= k < i ==> !arr2@.contains(arr1[k]),
    {
        if contains(arr2, arr1[i]) {
            proof {
                assert(arr2@.contains(arr1[i as int]));
            }
            return true;
        }
    }
    false
}

} // verus!