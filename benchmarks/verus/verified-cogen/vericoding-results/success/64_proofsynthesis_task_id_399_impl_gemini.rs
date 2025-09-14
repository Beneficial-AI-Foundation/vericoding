// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn bit_wise_xor(arr1: &Vec<i32>, arr2: &Vec<i32>) -> (result: Vec<i32>)

    requires
        arr1.len() == arr2.len(),

    ensures
        result.len() == arr1.len(),
        forall|i: int|
            0 <= i < result.len() ==> result[i] == #[trigger] arr1[i] ^ #[trigger] arr2[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added a decreases clause to the while loop to prove termination */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < arr1.len()
        invariant
            arr1.len() == arr2.len(),
            0 <= i <= arr1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == arr1@[j] ^ arr2@[j],
        decreases arr1.len() - i,
    {
        result.push(arr1[i] ^ arr2[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}