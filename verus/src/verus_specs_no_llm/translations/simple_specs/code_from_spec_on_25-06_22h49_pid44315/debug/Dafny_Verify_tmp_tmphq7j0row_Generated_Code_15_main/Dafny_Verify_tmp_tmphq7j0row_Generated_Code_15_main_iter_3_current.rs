use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
    // Main function can call other functions for testing
    let result = compute_value(5, 10);
    // The postcondition of compute_value already ensures result >= 0
    // So we don't need an additional assertion here in main
}

fn compute_value(n: int, k: int) -> (k_out: int)
    requires
        n > 0,
        k > n
    ensures
        k_out >= 0
{
    // Since k > n and n > 0, we know k > 0
    // We can return any non-negative value to satisfy the ensures clause
    // A simple implementation that satisfies the postcondition:
    k - n
}

// If we want to verify additional properties, we can create a separate proof function
proof fn verify_compute_value_properties() {
    let result = compute_value(5, 10);
    assert(result >= 0); // This follows from the ensures clause
}

}