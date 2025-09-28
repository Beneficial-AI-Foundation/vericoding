// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn all_elements_equals(arr: &Vec<i32>, element: i32) -> (result: bool)

    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> (arr[i] == element)),
// </vc-spec>
// <vc-code>
{
    for i in 0..arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|j: int| 0 <= j < i ==> arr[j] == element
    {
        if arr[i] != element {
            return false;
        }
    }
    true
}
// </vc-code>

}
fn main() {}