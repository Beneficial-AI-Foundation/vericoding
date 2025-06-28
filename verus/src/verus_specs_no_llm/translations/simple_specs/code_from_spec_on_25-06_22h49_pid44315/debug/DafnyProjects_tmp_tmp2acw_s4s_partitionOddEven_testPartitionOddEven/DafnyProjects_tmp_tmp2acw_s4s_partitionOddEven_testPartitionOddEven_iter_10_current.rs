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
    assert((n as int) % 2 == 0 || (n as int) % 2 == 1) by(nonlinear_arith);
    
    if (n as int) % 2 == 1 {
        assert(odd(n));
        assert(!even(n));
    } else {
        assert((n as int) % 2 == 0);
        assert(even(n));
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
    assert(0int % 2 == 0) by(nonlinear_arith);
}

proof fn one_is_odd()
    ensures odd(1)
{
    assert(1int % 2 == 1) by(nonlinear_arith);
}

proof fn succ_odd_is_even(n: nat)
    requires odd(n)
    ensures even(n + 1)
{
    // If n is odd, then n % 2 == 1
    // So (n + 1) % 2 == 0
    assert((n as int) % 2 == 1);
    assert(((n + 1) as int) % 2 == 0) by(nonlinear_arith);
}

proof fn succ_even_is_odd(n: nat)
    requires even(n)
    ensures odd(n + 1)
{
    // If n is even, then n % 2 == 0
    // So (n + 1) % 2 == 1
    assert((n as int) % 2 == 0);
    assert(((n + 1) as int) % 2 == 1) by(nonlinear_arith);
}

}