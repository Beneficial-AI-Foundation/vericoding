// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn pow2(n: nat) -> nat 
    decreases n
{
    if n == 0 {
        1nat
    } else {
        2nat * pow2((n - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): get_mask must be an ordinary function to be called from code. */
fn get_mask(bit_width: u32) -> u32 {
    (pow2(bit_width as nat) - 1) as u32
}
// </vc-helpers>

// <vc-spec>
fn invert(bit_width: u32, a: Vec<u32>) -> (result: Vec<u32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a@.len() ==> result@[i] == (pow2(bit_width as nat) - 1) - a@[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Call get_mask as a regular function. */
{
    let mut result: Vec<u32> = Vec::new();
    let mask: u32 = get_mask(bit_width);
    let mut i: usize = 0;
    let old_a_len = a.len();
    let old_bit_width = bit_width;

    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == mask - a@[j],
            a.len() == old_a_len,
            bit_width == old_bit_width,
            mask == (pow2(bit_width as nat) - 1) as u32
    {
        result.push(mask - a[i]);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}