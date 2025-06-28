use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
    // Main function can call other functions for testing
    // Use i32 instead of int for executable code
    let result = compute_value(5i32, 10i32);
    // The postcondition of compute_value already ensures result >= 0
    // So we don't need an additional assertion here in main
}

fn compute_value(n: i32, k: i32) -> (k_out: i32)
    requires
        n > 0,
        k > n,
        k - n <= 2147483647  // Ensure no overflow for i32
    ensures
        k_out >= 0
{
    // Since k > n and n > 0, we know k > 0
    // We can return any non-negative value to satisfy the ensures clause
    // A simple implementation that satisfies the postcondition:
    k - n
}

// Proof function to verify properties about compute_value
proof fn verify_compute_value_properties() {
    // We can reason about the mathematical properties directly
    // Since we know from the ensures clause that compute_value returns >= 0
    // when called with valid preconditions, we can assert this property
    assert(forall |n: int, k: int| n > 0 && k > n ==> k - n >= 0);
}

}