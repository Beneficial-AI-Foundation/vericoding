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
    /* code modified by LLM (iteration 5): Fixed invariant preservation and assertions */
    let mut result = Vec::new();
    let mut i = 0;
    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            forall|j: int| 0 <= j < result.len() ==> (arr1@.contains(#[trigger] result[j]) && !arr2@.contains(#[trigger] result[j])),
            forall|j: int| 0 <= j < i ==> (arr2@.contains(#[trigger] arr1@[j]) || result@.contains(#[trigger] arr1@[j])),
        decreases arr1.len() - i
    {
        let elem = arr1[i];
        let mut found = false;
        let mut j = 0;
        while j < arr2.len()
            invariant
                0 <= j <= arr2.len(),
                found ==> arr2@.contains(elem),
                !found ==> forall|k: int| 0 <= k < j ==> arr2[k] != elem,
            decreases arr2.len() - j
        {
            if arr2[j] == elem {
                found = true;
                break;
            }
            j = j + 1;
        }
        if !found {
            proof {
                assert(elem == arr1@[i as int]);
                assert(arr1@.contains(elem));
                assert(forall|k: int| 0 <= k < arr2.len() ==> arr2[k] != elem);
            }
            result.push(elem);
            proof {
                assert(result[result.len() - 1] == elem);
                assert(result@[result.len() - 1] == elem);
                assert(arr1@.contains(elem));
                assert(!arr2@.contains(elem));
            }
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}