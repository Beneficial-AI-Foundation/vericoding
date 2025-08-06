use vstd::prelude::*;

verus! {

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    // post-conditions-start
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
    // post-conditions-end
{
    return false;  // TODO: Remove this line and implement the function body
}

fn any_value_exists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
    // post-conditions-start
    ensures
        result == exists|k: int| 0 <= k < arr1.len() && arr2@.contains(#[trigger] arr1[k]),
    // post-conditions-end
{
    return false;  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}
