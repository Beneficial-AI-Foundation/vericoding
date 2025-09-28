// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 3): Fixed trigger annotation in loop invariant */
    let mut result = Vec::new();
    let n = arr1.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == arr1.len(),
            n == arr2.len(),
            result@.len() == i as int,
            forall|j: int| 0 <= j < i ==> result[j] == (arr1[j] % arr2[j]),
            forall|j: int| 0 <= j < arr2.len() ==> arr2[j] != 0,
            forall|j: int| 0 <= j < arr1.len() ==> (i32::MIN <= #[trigger] (arr1[j] % arr2[j]) <= i32::MAX),
        decreases n - i
    {
        let val = arr1[i] % arr2[i];
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}