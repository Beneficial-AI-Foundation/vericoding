use vstd::prelude::*;

verus! {

// <vc-helpers>
fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|m: int| 0 <= m < i ==> (arr[m] != key),
    {
        if (arr[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn any_value_exists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
    // post-conditions-start
    ensures
        result == exists|k: int| 0 <= k < arr1.len() && arr2@.contains(#[trigger] arr1[k]),
    // post-conditions-end
// </vc-spec>

// <vc-code>
fn any_value_exists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)
    ensures
        result == (exists|k: int| 0 <= k < arr1.len() && arr2@.contains(arr1[k])),
{
    let mut i = 0;
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            forall|m: int| 0 <= m < i ==> !arr2@.contains(arr1[m]),
    {
        if contains(arr2, arr1[i]) {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-code>

} // verus!

fn main() {}