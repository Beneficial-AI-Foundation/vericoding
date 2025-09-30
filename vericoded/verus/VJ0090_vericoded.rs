// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn element_wise_multiplication(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)

    requires
        arr1.len() == arr2.len(),
        forall|i: int|
            (0 <= i < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[i] * arr2[i]) <= i32::MAX),

    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> #[trigger] result[i] == #[trigger] (arr1[i] * arr2[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to the loop */
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < arr1.len()
        invariant
            arr1.len() == arr2.len(),
            i <= arr1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j] == #[trigger] (arr1[j] * arr2[j]),
            forall|k: int|
                (0 <= k < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[k] * arr2[k]) <= i32::MAX),
        decreases arr1.len() - i
    {
        let product = arr1[i] * arr2[i];
        result.push(product);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}