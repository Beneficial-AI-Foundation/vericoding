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

// </vc-helpers>

// <vc-spec>
fn invert(bit_width: u32, a: Vec<u32>) -> (result: Vec<u32>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a@.len() ==> result@[i] == (pow2(bit_width as nat) - 1) - a@[i]
// </vc-spec>
// <vc-code>
{
    let mask = if bit_width == 0 {
        0u32
    } else if bit_width < 32 {
        (1u32 << bit_width) - 1
    } else {
        u32::MAX
    };
    let mut result = Vec::new();
    for i in 0..a.len()
    {
        let inverted = mask - a[i];
        result.push(inverted);
    }
    result
}
// </vc-code>


}
fn main() {}