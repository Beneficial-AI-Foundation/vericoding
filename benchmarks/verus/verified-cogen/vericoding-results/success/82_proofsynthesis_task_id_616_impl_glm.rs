// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): kept lemma to extract arr2[i] != 0 */
proof fn arr2_non_zero(arr2: &Vec<u32>, i: int)
    requires
        0 <= i < arr2.len(),
        forall|j: int| 0 <= j < arr2.len() ==> arr2[j] != 0,
    ensures
        arr2[i] != 0,
{
}
// </vc-helpers>

// <vc-spec>
fn element_wise_module(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)

    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] % arr2[i]) <= i32::MAX),

    ensures
        result@.len() == arr1@.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] % arr2[i]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Added global arr2 non-zero condition to loop invariant with trigger to satisfy lemma precondition */
{
    let mut result = Vec::with_capacity(arr1.len());
    for i in 0..arr1.len()
        invariant
            arr1.len() == arr2.len(),
            i <= arr1.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == arr1[j] % arr2[j],
            forall|j: int| 0 <= j < arr2.len() ==> #[trigger] arr2[j] != 0,
    {
        proof {
            arr2_non_zero(arr2, i as int);
        }
        result.push(arr1[i] % arr2[i]);
    }
    result
}
// </vc-code>

}
fn main() {}