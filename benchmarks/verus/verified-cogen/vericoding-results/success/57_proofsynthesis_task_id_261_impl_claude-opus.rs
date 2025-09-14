// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < arr1.len()
        invariant
            i <= arr1.len(),
            result.len() == i,
            arr1.len() == arr2.len(),
            forall|j: int| 0 <= j < i ==> result[j] == arr1[j] / arr2[j],
            forall|j: int| 0 <= j < arr2.len() ==> arr2[j] != 0,
            forall|m: int| 0 <= m < arr1.len() ==> (u32::MIN <= #[trigger] arr1[m] / #[trigger] arr2[m] <= u32::MAX),
        decreases arr1.len() - i,
    {
        let quotient = arr1[i] / arr2[i];
        result.push(quotient);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}