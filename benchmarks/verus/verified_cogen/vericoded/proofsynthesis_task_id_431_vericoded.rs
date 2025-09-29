// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added decreases clause to while loop */
fn contains(list: &Vec<i32>, element: i32) -> (result: bool)
    ensures
        result == exists|i: int| 0 <= i < list.len() && list[i] == element,
{
    let mut i = 0;
    while i < list.len()
        invariant
            0 <= i <= list.len(),
            !(exists|k: int| 0 <= k < i && list[k] == element),
        decreases list.len() - i,
    {
        if list[i] == element {
            return true;
        }
        i = i + 1;
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
{
    /* code modified by LLM (iteration 2): added decreases clause to while loop */
    let mut i = 0;
    while i < list1.len()
        invariant
            0 <= i <= list1.len(),
            !(exists|k: int, j: int|
                0 <= k < i && 0 <= j < list2.len() && list1[k] == list2[j]),
        decreases list1.len() - i,
    {
        let elem = list1[i];
        if contains(list2, elem) {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

}
fn main() {}