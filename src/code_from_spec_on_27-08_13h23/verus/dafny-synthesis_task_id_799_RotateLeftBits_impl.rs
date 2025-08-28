use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this fix
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn rotate_left_bits(n: u32, d: int) -> (result: u32)
    requires 0 <= d < 32
    ensures result == ((n << d) | (n >> (32 - d)))
// </vc-spec>
// </vc-spec>

// <vc-code>
fn rotate_left_bits(n: u32, d: int) -> (result: u32)
    requires 0 <= d < 32
    ensures result == ((n << d) | (n >> (32 - d)))
{
    let left_shift = n << d;
    let right_shift = n >> (32 - d);
    let result = left_shift | right_shift;
    result
}
// </vc-code>

fn main() {
}

}