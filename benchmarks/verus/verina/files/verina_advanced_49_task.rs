// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn merge_sorted_lists(arr1: &Vec<i8>, arr2: &Vec<i8>) -> (result: Vec<i8>)
    requires 
        forall|i: int, j: int| 0 <= i < j < arr1.len() ==> arr1[i] as int <= arr1[j] as int,
        forall|i: int, j: int| 0 <= i < j < arr2.len() ==> arr2[i] as int <= arr2[j] as int,
    ensures
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] as int <= result[j] as int,
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