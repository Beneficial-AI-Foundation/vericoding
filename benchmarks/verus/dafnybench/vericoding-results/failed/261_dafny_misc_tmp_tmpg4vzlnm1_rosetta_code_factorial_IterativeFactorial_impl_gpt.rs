use vstd::prelude::*;

verus! {

// recursive definition of factorial
spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
}

// iterative implementation of factorial

// <vc-helpers>
proof fn factorial_succ(n: nat)
    ensures factorial(n + 1) == (n + 1) * factorial(n)
{
    assert(n + 1 != 0);
    assert(factorial(n + 1) == (n + 1) * factorial((n + 1 - 1) as nat));
    assert(n + 1 - 1 == n);
}

proof fn mul_nat_ge_right(y: nat, x: nat)
    requires x >= 1
    ensures y <= x * y
{
    assert(x * y >= 1 * y);
    assert(1 * y == y);
}

proof fn factorial_monotonic_le(a: nat, b: nat)
    requires a <= b
    ensures factorial(a) <= factorial(b)
    decreases b - a
{
    if a == b {
    } else {
        assert(a < b);
        assert(b >= 1);
        factorial_monotonic_le(a, b - 1);
        factorial_succ(b - 1);
        // factorial(b) == b * factorial(b - 1) >= factorial(b - 1)
        mul_nat_ge
// </vc-helpers>

// <vc-spec>
fn iterative_factorial(n: u32) -> (result: u32)
    requires n < 13, // prevent overflow
    ensures result == factorial(n as nat)
// </vc-spec>
// <vc-code>
proof fn factorial_succ(n: nat)
    ensures factorial(n + 1) == (n + 1) * factorial(n)
{
    assert(n + 1 != 0);
    assert(factorial(n + 1) == (n + 1) * factorial((n + 1 - 1) as nat));
    assert(n + 1 - 1 == n);
}

proof fn mul_nat_ge_right(y: nat, x: nat)
    requires x >= 1
    ensures y <= x * y
{
    assert(x * y >= 1 * y);
    assert(1 * y == y);
}

proof fn factorial_monotonic_le(a: nat, b: nat)
    requires a <= b
    ensures factorial(a) <= factorial(b)
    decreases b - a
{
    if a == b {
    } else {
        assert(a < b);
        assert(b >= 1);
        factorial_monotonic_le(a, b - 1);
        factorial_succ(b - 1);
        // factorial(b) == b * factorial(b - 1) >= factorial(b - 1)
        mul_nat_ge
// </vc-code>

fn main() {}

}