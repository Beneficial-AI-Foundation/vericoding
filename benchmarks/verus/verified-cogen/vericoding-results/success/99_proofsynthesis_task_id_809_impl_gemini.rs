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
    /* code modified by LLM (iteration 2): Added a decreases clause to prove loop termination. */
    let mut i: usize = 0;
    while i < arr1.len()
        invariant
            arr1.len() == arr2.len(),
            0 <= i <= arr1.len(),
            forall|j: int| 0 <= j < i ==> arr1@[j] > arr2@[j],
        decreases arr1.len() - i
    {
        if arr1[i] <= arr2[i] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}