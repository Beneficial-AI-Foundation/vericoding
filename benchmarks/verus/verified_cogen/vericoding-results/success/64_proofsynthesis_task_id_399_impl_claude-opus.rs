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
    /* code modified by LLM (iteration 3): Fixed loop invariant and bounds checking */
    let mut result = Vec::new();
    let n = arr1.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == arr1.len(),
            n == arr2.len(),
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == arr1[j] ^ arr2[j],
        decreases n - i,
    {
        let val = arr1[i] ^ arr2[i];
        result.push(val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}