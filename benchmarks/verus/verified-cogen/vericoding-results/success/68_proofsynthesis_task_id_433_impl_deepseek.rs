// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Add decreases clause to fix recursion */
spec fn is_greater_helper(arr: Seq<int>, number: int, i: int) -> bool
    decreases arr.len() - i
{
    if i >= arr.len() {
        true
    } else {
        number > arr[i] && is_greater_helper(arr, number, i + 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn is_greater(arr: &Vec<i32>, number: i32) -> (result: bool)

    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> number > arr[i]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Maintain original implementation with loop */
{
    let mut index = 0;
    while index < arr.len()
        invariant
            0 <= index <= arr.len(),
            forall|j: int| 0 <= j < index ==> number > arr[j],
        decreases arr.len() - index
    {
        if number <= arr[index] {
            return false;
        }
        index = index + 1;
    }
    true
}
// </vc-code>

}
fn main() {}