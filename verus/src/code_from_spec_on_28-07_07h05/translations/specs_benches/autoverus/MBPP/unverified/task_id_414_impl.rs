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
    for i in 0..arr1.len()
        invariant
            forall|j: int| 0 <= j < i ==> !arr2@.contains(arr1[j]),
    {
        /* code modified by LLM (iteration 1): replaced spec-mode arr2@.contains() with exec-mode contains() function call */
        if contains(arr2, arr1[i]) {
            return true;
        }
    }
    false
}

} // verus!