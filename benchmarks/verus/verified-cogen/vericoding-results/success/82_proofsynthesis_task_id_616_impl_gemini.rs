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
    /* code modified by LLM (iteration 2): [Added missing trigger annotation to loop invariant] */
    let mut result: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < arr1.len()
        invariant
            arr1.len() == arr2.len(),
            forall|j: int| 0 <= j < arr2.len() ==> arr2[j] != 0,
            forall|j: int| (0 <= j < arr1.len()) ==> (i32::MIN <= #[trigger] (arr1[j] % arr2[j]) <= i32::MAX),
            i <= arr1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == arr1[j] % arr2[j],
        decreases arr1.len() - i,
    {
        let val1 = arr1[i];
        let val2 = arr2[i];
        let mod_res = val1 % val2;
        result.push(mod_res);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}