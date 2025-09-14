// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn element_wise_divide(arr1: &Vec<u32>, arr2: &Vec<u32>) -> (result: Vec<u32>)

    requires
        arr1.len() == arr2.len(),
        forall|i: int| 0 <= i < arr2.len() ==> arr2[i] != 0,
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] / arr2[i]) <= i32::MAX),

    ensures
        result@.len() == arr1@.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] / arr2[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added triggers to loop invariants to fix verification error */
    let mut result: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < arr1.len()
        invariant
            arr1.len() == arr2.len(),
            forall|k: int| 0 <= k < arr2.len() ==> #[trigger] arr2[k] != 0,
            forall|k: int| 0 <= k < arr1.len() ==> i32::MIN <= (#[trigger] arr1[k]) / arr2[k] <= i32::MAX,
            0 <= i <= arr1.len(),
            result.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> #[trigger] result[j] == arr1[j] / arr2[j],
        decreases arr1.len() - i
    {
        let val = arr1[i] / arr2[i];
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}