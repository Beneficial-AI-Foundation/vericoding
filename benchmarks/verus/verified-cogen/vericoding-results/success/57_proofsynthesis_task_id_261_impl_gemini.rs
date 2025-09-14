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
    /* code modified by LLM (iteration 2): added invariants to prove division safety */
    let mut result = Vec::new();
    let mut i: usize = 0;

    while i < arr1.len()
        invariant
            arr1.len() == arr2.len(),
            forall|k: int| 0 <= k < arr2.len() ==> arr2[k] != 0,
            0 <= i <= arr1.len(),
            result.len() == i as int,
            forall|j: int| 0 <= j < i ==> result[j] == arr1[j] / arr2[j],
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