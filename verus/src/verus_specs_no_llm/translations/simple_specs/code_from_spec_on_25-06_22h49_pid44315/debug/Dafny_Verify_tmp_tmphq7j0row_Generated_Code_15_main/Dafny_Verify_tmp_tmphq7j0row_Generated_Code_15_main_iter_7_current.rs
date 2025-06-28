use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
    // Main function can call other functions for testing
    let result = compute_value(5int, 10int);
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

// Proof function to verify properties about compute_value
proof fn verify_compute_value_properties() {
    // We can reason about the mathematical properties directly
    // Since we know from the ensures clause that compute_value returns >= 0
    // when called with valid preconditions, we can assert this property
    assert(forall |n: int, k: int| n > 0 && k > n ==> k - n >= 0);
}

}