// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): keep simple executable xor helper for clarity */
fn bitxor_i32(a: i32, b: i32) -> i32 { a ^ b }
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
    /* code modified by LLM (iteration 4): strengthen loop invariants by relating n to input lengths and remove failing assertion */
    let n = arr1.len();
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == arr1.len(),
            n == arr2.len(),
            i <= n,
            result.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> result[j] == arr1[j] ^ arr2[j],
        decreases n - i
    {
        assert(i < arr1.len());
        assert(i < arr2.len());
        let x = arr1[i] ^ arr2[i];
        result.push(x);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}