// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): fixed function signature to bind result variable */
fn contains(list: &Vec<i32>, element: i32) -> (result: bool)
    ensures result == (exists|j: int| 0 <= j < list.len() && list@[j] == element)
{
    for i in 0..list.len()
        invariant 0 <= i <= list.len(),
        forall|k: int| 0 <= k < i ==> list@[k] != element
    {
        if list[i] == element {
            return true;
        }
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn has_common_element(list1: &Vec<i32>, list2: &Vec<i32>) -> (result: bool)

    ensures
        result == (exists|i: int, j: int|
            0 <= i < list1.len() && 0 <= j < list2.len() && (list1[i] == list2[j])),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): updated comment to reflect current iteration */
{
    for i in 0..list1.len()
        invariant
            0 <= i <= list1.len(),
            forall|k: int, j: int| (0 <= k < i && 0 <= j < list2.len()) ==> list1@[k] != list2@[j]
    {
        if contains(list2, list1[i]) {
            return true;
        }
    }
    false
}
// </vc-code>

}
fn main() {}