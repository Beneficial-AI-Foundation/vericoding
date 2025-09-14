// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn remove_elements(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)

    ensures
        forall|i: int|
            0 <= i < result.len() ==> (arr1@.contains(#[trigger] result[i]) && !arr2@.contains(
                #[trigger] result[i],
            )),
        forall|i: int|
            0 <= i < arr1.len() ==> (arr2@.contains(#[trigger] arr1[i]) || result@.contains(
                #[trigger] arr1[i],
            )),
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut i = 0;

    while i < arr1.len()
        invariant (
            forall|j: int| 0 <= j < result.len() ==> (
                arr1@.contains(#[trigger] result[j]) && !arr2@.contains(#[trigger] result[j])
            ),
            forall|j: int| 0 <= j < result.len() ==> result.count(result[j]) == 1,
            result.len() <= arr1.len(),
            i <= arr1.len(),
            forall|k: int| 0 <= k < i ==> (
                arr2@.contains(#[trigger] arr1@[k]) || result@.contains(#[trigger] arr1@[k])
            )
        )
        decreases arr1.len() - i
    {
        let current_element = arr1@[i];
        if !arr2@.contains(current_element) {
            result.push(current_element);
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}