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
    /* code modified by LLM (iteration 5): Replaced type-unsafe int variables with usize for exec code compatibility, simplified logic using sequence contains for checking presence in arr2 */
    let mut result: Vec<i32> = Vec::new();
    for i in 0..arr1.len()
        invariant
            arr1.len() == arr1@.len(),
            arr2.len() == arr2@.len(),
            0 <= (i as int) <= arr1@.len(),
            forall|k: int| 0 <= k < (i as int) ==> (arr2@.contains(arr1@[k]) || result@.contains(#[trigger] arr1@[k])),
            forall|j: int| 0 <= j < result.len() ==> (arr1@.contains(#[trigger] result@[j]) && !arr2@.contains(#[trigger] result@[j])),
            forall|j: int| 0 <= j < result.len() ==> exists|y: int| 0 <= y < (i as int) && result@[j] == arr1@[y]
    {
        if !arr2@.contains(arr1@[(i as int)]) {
            result.push(arr1[i]);
        }
    }
    result
}
// </vc-code>

}
fn main() {}