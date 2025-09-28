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
    // Since d is guaranteed to be in range [0, 32), we can safely convert
    assert(0 <= d < 32);
    
    // Perform the rotation using standard shift operators
    // The precondition ensures d is valid for these operations
    let result = (n << d) | (n >> (32 - d));
    
    result
}
// </vc-code>

fn main() {
}

}