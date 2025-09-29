// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): added decreases clause to fix compilation error */
fn contains_value(arr2: &Vec<i32>, val: i32) -> (result: bool)
    ensures
        result == arr2@.contains(val),
{
    let mut j = 0;
    while j < arr2.len()
        invariant
            0 <= j <= arr2.len(),
            forall|k: int| 0 <= k < j ==> arr2[k] != val,
        decreases arr2.len() - j
    {
        if arr2[j] == val {
            return true;
        }
        j += 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn any_value_exists(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: bool)

    ensures
        result == exists|k: int| 0 <= k < arr1.len() && arr2@.contains(#[trigger] arr1[k]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): added decreases clause to fix compilation error */
    let mut i = 0;
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            forall|k: int| 0 <= k < i ==> !arr2@.contains(arr1[k]),
        decreases arr1.len() - i
    {
        if contains_value(arr2, arr1[i]) {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-code>

}
fn main() {}