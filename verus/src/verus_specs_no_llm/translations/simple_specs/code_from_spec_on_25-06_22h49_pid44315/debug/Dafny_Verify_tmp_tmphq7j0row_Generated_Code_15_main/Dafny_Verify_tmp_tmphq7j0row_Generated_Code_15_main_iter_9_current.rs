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
    // Since k > n, we have k - n > 0, which satisfies k_out >= 0
    // We need to prove this relationship holds
    proof {
        // Since k > n, we know k - n > 0, therefore k - n >= 0
        assert(k > n);
        assert(k - n > 0);
        assert(k - n >= 0);
    }
    k - n
}

// Proof function to verify properties about compute_value
proof fn verify_compute_value_properties() {
    // The mathematical property we want to verify
    // If k > n, then k - n > 0, which means k - n >= 0
    assert(forall |n: int, k: int| k > n ==> k - n > 0);
    assert(forall |n: int, k: int| k > n ==> k - n >= 0);
}

}