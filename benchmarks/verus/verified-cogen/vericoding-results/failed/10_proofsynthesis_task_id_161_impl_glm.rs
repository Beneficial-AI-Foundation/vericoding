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
/* code modified by LLM (iteration 5): replaced contains call with explicit loop */
{
    let mut result = Vec::new();
    for i in 0..arr1.len()
        invariant
            forall|j: int| 0 <= j < result.len() ==> (arr1@.contains(#[trigger] result[j]) && !arr2@.contains(#[trigger] result[j])),
            forall|j: int| 0 <= j < i ==> (arr2@.contains(#[trigger] arr1[j]) || result@.contains(#[trigger] arr1[j])),
    {
        let elem = arr1[i];
        let mut found = false;
        for j in 0..arr2.len() {
            if arr2[j] == elem {
                found = true;
                break;
            }
        }
        if !found {
            result.push(elem);
        }
    }
    result
}
// </vc-code>

}
fn main() {}