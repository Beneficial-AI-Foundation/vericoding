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
proof fn factorial_monotonic(a: nat, b: nat)
    requires a <= b
    ensures factorial(a) <= factorial(b)
    decreases b
{
    if a == b {
    } else if b == 0 {
    } else {
        factorial_monotonic(a, b - 1);
        assert(factorial(a) <= factorial(b - 1));
        assert(factorial(b) == b * factorial(b - 1));
        assert(factorial(b - 1) <= b * factorial(b - 1));
    }
}

proof fn factorial12_within_u32()
    ensures factorial(12) == 479001600
    ensures 479001600 <= u32::MAX
{
    let f0 = factorial(0);
    assert(f0 == 1);
    let f1 = factorial(1);
    assert(f1 == 1);
    let f2 = factorial(2);
    assert(f2 == f1 * 2);
    assert(f2 == 2);
    let f3 = factorial(3);
    assert(f3 == f2 * 3);
    assert(f3 == 6);
    let f4 = factorial(4);
    assert(f4 == f3 * 4);
    assert(f4 == 24);
    let f5 = factorial(5);
    assert(f5 == f4 * 5);
    assert(f5 == 120);
    let f6 = factorial(6);
    assert(f6 == f5 * 6);
    assert(f6 == 720);
    let f7 = factorial(7);
    assert(f7 == f6 * 7);
    assert(f7 == 5040);
    let f8 = factorial(8);
    assert(f8 == f7 * 8);
    assert(f8 == 40320);
    let f9 = factorial(9);
    assert(f9 == f8 * 9);
    assert(f9 == 362880);
    let f10 = factorial(10);
    assert(f10 == f9 * 10);
    assert(f10 == 3628800);
    let f11 = factorial(11);
    assert(f11 == f10 * 11);
    assert(f11 == 39916800);
    let f12 = factorial(12);
    assert(f12 == f11 * 12);
    assert(f12 == 479001600);
    assert(479001600 <= u32::MAX);
}
// </vc-helpers>

// <vc-spec>
fn iterative_factorial(n: u32) -> (result: u32)
    requires n < 13, // prevent overflow
    ensures result == factorial(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut i: u32 = 1;
    let mut result: u32 = 1;
    while i <= n
        invariant
            1 <= i <= n + 1,
            result == factorial((i - 1) as nat)
    {
        proof {
            let k = (i - 1) as nat;
            assert(k <= 11);
            factorial_monotonic(k, 11);
            assert(factorial(k) <= factorial(11));
            assert(factorial(11) * (i as nat) <= factorial(11) * 12);
            assert(factorial(11) * 12 == factorial(12));
            assert(factorial(12) <= u32::MAX as nat) by { factorial12_within_u32(); }
        }
        result = result * i;
        i = i + 1;
    }
    result
}
// </vc-code>

fn main() {}

}