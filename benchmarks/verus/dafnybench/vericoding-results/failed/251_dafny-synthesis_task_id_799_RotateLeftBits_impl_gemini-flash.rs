use vstd::prelude::*;

verus! {

// <vc-helpers>
/// This helper function computes the left rotation of a u32 number.
/// This is used to prove the postcondition in the `rotate_left_bits` function.
spec fn rotate_left_bits_spec(n: u32, d: u32) -> u32
    requires 0 <= d && d < 32
{
    ((n << d) | (n >> (32u32 - d)))
}
// </vc-helpers>

// <vc-spec>
fn rotate_left_bits(n: u32, d: int) -> (result: u32)
    requires 0 <= d < 32
    ensures result == ((n << d) | (n >> (32 - d)))
// </vc-spec>
// <vc-code>
{
    // The core operation is exactly as specified by the ensures clause.
    // We need to prove that this direct implementation satisfies the postcondition.
    let d_u32 = d as u32; // Cast int to u32 for bitwise operations

    let shifted_left = n << d_u32;
    let shifted_right = n >> (32u32 - d_u32);
    let result = shifted_left | shifted_right;

    // Proof that the implementation matches the specification.
    proof {
        // We are directly computing the right-hand side of the ensures clause.
        // The `result` variable is assigned the expression `((n << d) | (n >> (32 - d)))`.
        // Therefore, `result` is equal to `rotate_left_bits_spec(n, d)`.

        // Prove that the cast from int to u32 is valid under the precondition
        // Verus automatically understands that if d is an int within 0 <= d < 32,
        // then d as u32 will be equal to d.
        assert(d_u32 == d) by (bit_vector); // This holds because 0 <= d < 32 and d is an int

        assert(shifted_left == (n << d_u32));
        assert(shifted_right == (n >> (32u32 - d_u32)));
        assert(result == ((n << d_u32) | (n >> (32u32 - d_u32))));

        assert(result == rotate_left_bits_spec(n, d_u32));
    }

    result
}
// </vc-code>

fn main() {
}

}