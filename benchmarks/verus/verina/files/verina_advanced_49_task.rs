// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn merge_sorted_lists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)
    requires 
        forall|i: int, j: int| 0 <= i < j < arr1.len() ==> arr1[i] <= arr1[j],
        forall|i: int, j: int| 0 <= i < j < arr2.len() ==> arr2[i] <= arr2[j],
    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] <= result[j],
        result.len() == arr1.len() + arr2.len(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}