use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn rotate_left_bits(n: u32, d: int) -> (result: u32)
    requires 0 <= d < 32
    ensures result == ((n << d) | (n >> (32 - d)))
// </vc-spec>
// <vc-code>
{
    proof {
        assert(0 <= d < 32);
        assert(d >= 0);
        assert(d < 32);
    }
    let d_u32 = d as u32;
    let shifted_left = n << d_u32;
    let shifted_right = n >> (32u32 - d_u32);
    shifted_left | shifted_right
}
// </vc-code>

fn main() {
}

}