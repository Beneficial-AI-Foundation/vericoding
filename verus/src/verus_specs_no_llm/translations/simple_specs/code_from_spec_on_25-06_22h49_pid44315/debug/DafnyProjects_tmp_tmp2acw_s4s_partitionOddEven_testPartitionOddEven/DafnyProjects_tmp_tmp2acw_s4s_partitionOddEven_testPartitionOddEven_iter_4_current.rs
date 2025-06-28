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
    // The proof is automatic given the definitions
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
}

proof fn one_is_odd()
    ensures odd(1)
{
}

proof fn succ_odd_is_even(n: nat)
    requires odd(n)
    ensures even(n + 1)
{
}

proof fn succ_even_is_odd(n: nat)
    requires even(n)
    ensures odd(n + 1)
{
}

}