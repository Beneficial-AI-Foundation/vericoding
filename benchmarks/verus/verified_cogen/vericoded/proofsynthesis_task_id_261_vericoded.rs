// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): no helpers in this problem */
// </vc-helpers>

// <vc-spec>
fn element_wise_division(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)

    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|m: int|
            0 <= m < arr1.len() ==> (u32::MIN <= #[trigger] arr1[m] / #[trigger] arr2[m]
                <= u32::MAX),

    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] / arr2[i]),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed type mismatch in assert statement within the proof block */
{
    let mut result = Vec::new();
    let mut i = 0;

    while i < arr1.len()
        invariant
            0 <= i <= arr1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result.view()[j] == (arr1.view()[j] / arr2.view()[j]),
            arr1.len() == arr2.len(),
            forall|k: int| 0 <= k < arr2.len() ==> arr2.view()[k] != 0,
        decreases arr1.len() - i
    {
        // Prove that arr2[i] is not zero for the current iteration
        proof {
            assert(0 <= i && i < arr2.len() as int); // Establish bounds for i
            assert(arr2.view()[i as int] != 0);
        }
        result.push(arr1[i] / arr2[i]);
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}