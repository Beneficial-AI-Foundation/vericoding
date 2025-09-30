// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_smaller(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)

    requires
        arr1.len() == arr2.len(),

    ensures
        result == (forall|i: int| 0 <= i < arr1.len() ==> arr1[i] > arr2[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed postcondition proof by establishing loop invariant correctly */
    let mut index = 0;
    while index < arr1.len()
        invariant
            0 <= index <= arr1.len(),
            arr1.len() == arr2.len(),
            forall|i: int| 0 <= i < index ==> arr1@[i] > arr2@[i],
        decreases arr1.len() - index
    {
        if arr1[index] <= arr2[index] {
            return false;
        }
        index += 1;
    }
    true
}
// </vc-code>

}
fn main() {}