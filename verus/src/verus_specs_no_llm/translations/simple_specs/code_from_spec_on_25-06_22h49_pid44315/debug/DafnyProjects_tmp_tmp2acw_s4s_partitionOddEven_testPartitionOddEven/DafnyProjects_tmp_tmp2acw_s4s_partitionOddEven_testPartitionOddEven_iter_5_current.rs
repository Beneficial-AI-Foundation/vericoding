verus! {

use builtin::*;
use builtin_macros::*;

fn main() {
}

spec fn odd(n: nat) -> bool {
    (n as int) % 2 == 1
}

spec fn even(n: nat) -> bool {
    (n as int) % 2 == 0
}

// Helper proof function to demonstrate the relationship between odd and even
proof fn odd_even_relationship(n: nat)
    ensures odd(n) == !even(n)
{
    // For any integer, n % 2 is either 0 or 1
    // If n % 2 == 1, then odd(n) is true and even(n) is false
    // If n % 2 == 0, then odd(n) is false and even(n) is true
    // This relationship holds by the definitions and properties of modular arithmetic
    assert((n as int) % 2 == 0 || (n as int) % 2 == 1);
    if (n as int) % 2 == 1 {
        assert(odd(n));
        assert(!(n as int) % 2 == 0);
        assert(!even(n));
    } else {
        assert((n as int) % 2 == 0);
        assert(even(n));
        assert(!((n as int) % 2 == 1));
        assert(!odd(n));
    }
}

// Additional helper spec functions that might be useful
spec fn is_odd_nat(n: nat) -> bool {
    odd(n)
}

spec fn is_even_nat(n: nat) -> bool {
    even(n)
}

// Proof functions to establish basic properties
proof fn zero_is_even()
    ensures even(0)
{
    assert(0int % 2 == 0);
}

proof fn one_is_odd()
    ensures odd(1)
{
    assert(1int % 2 == 1);
}

proof fn succ_odd_is_even(n: nat)
    requires odd(n)
    ensures even(n + 1)
{
    // If n is odd, then n % 2 == 1
    // So (n + 1) % 2 == (1 + 1) % 2 == 2 % 2 == 0
    assert((n as int) % 2 == 1);
    assert(((n + 1) as int) % 2 == 0) by {
        // This follows from modular arithmetic properties
        // When n ≡ 1 (mod 2), then n + 1 ≡ 0 (mod 2)
    };
}

proof fn succ_even_is_odd(n: nat)
    requires even(n)
    ensures odd(n + 1)
{
    // If n is even, then n % 2 == 0
    // So (n + 1) % 2 == (0 + 1) % 2 == 1 % 2 == 1
    assert((n as int) % 2 == 0);
    assert(((n + 1) as int) % 2 == 1) by {
        // This follows from modular arithmetic properties
        // When n ≡ 0 (mod 2), then n + 1 ≡ 1 (mod 2)
    };
}

}