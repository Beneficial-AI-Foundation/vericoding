use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
    // Main function can call other functions for testing
    let result = compute_value(5, 10);
    assert(result >= 0);
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

}