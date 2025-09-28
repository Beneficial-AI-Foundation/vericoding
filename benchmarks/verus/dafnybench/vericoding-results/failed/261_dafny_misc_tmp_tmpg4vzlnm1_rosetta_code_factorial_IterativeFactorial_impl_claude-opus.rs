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
// Lemma to help prove that multiplying factorial(i) by (i+1) gives factorial(i+1)
proof fn factorial_step(i: nat)
    ensures factorial((i + 1) as nat) == (i + 1) * factorial(i)
{
    // This follows directly from the recursive definition of factorial
    // When i + 1 > 0, factorial(i + 1) = (i + 1) * factorial(i)
}

// Helper to compute specific factorial values
proof fn factorial_values()
    ensures 
        factorial(0) == 1,
        factorial(1) == 1,
        factorial(2) == 2,
        factorial(3) == 6,
        factorial(4) == 24,
        factorial(5) == 120,
        factorial(6) == 720,
        factorial(7) == 5040,
        factorial(8) == 40320,
        factorial(9) == 362880,
        factorial(10) == 3628800,
        factorial(11) == 39916800,
        factorial(12) == 479001600,
{
    // Unfold the recursive definition step by step
    assert(factorial(0) == 1);
    assert(factorial(1) == 1 * factorial(0) == 1 * 1 == 1);
    assert(factorial(2) == 2 * factorial(1) == 2 * 1 == 2);
    assert(factorial(3) == 3 * factorial(2) == 3 * 2 == 6);
    assert(factorial(4) == 4 * factorial(3) == 4 * 6 == 24);
    assert(factorial(5) == 5 * factorial(4) == 5 * 24 == 120);
    assert(factorial(6) == 6 * factorial(5) == 6 * 120 == 720);
    assert(factorial(7) == 7 * factorial(6) == 7 * 720 == 5040);
    assert(factorial(8) == 8 * factorial(7) == 8 * 5040 == 40320);
    assert(factorial(9) == 9 * factorial(8) == 9 * 40320 == 362880);
    assert(factorial(10) == 10 * factorial(9) == 10 * 362880 == 3628800);
    assert(factorial(11) == 11 * factorial(10) == 11 * 3628800 == 39916800);
    assert(factorial(12) == 12 * factorial(11) == 12 * 39916800 == 479001600);
}

// Helper to prove overflow bounds
proof fn factorial_bound(i: nat)
    ensures i < 13 ==> factorial(i) * (i + 1) < 0x100000000
    decreases i
{
    factorial_values();
    if i == 0 {
        assert(factorial(0) * 1 == 1 * 1 == 1);
        assert(1 < 0x100000000);
    } else if i < 13 {
        // Compute bounds for small factorials
        if i == 1 {
            assert(factorial(1) * 2 == 1 * 2 == 2);
            assert(2 < 0x100000000);
        } else if i == 2 {
            assert(factorial(2) * 3 == 2 * 3 == 6);
            assert(6 < 0x100000000);
        } else if i == 3 {
            assert(factorial(3) * 4 == 6 * 4 == 24);
            assert(24 < 0x100000000);
        } else if i == 4 {
            assert(factorial(4) * 5 == 24 * 5 == 120);
            assert(120 < 0x100000000);
        } else if i == 5 {
            assert(factorial(5) * 6 == 120 * 6 == 720);
            assert(720 < 0x100000000);
        } else if i == 6 {
            assert(factorial(6) * 7 == 720 * 7 == 5040);
            assert(5040 < 0x100000000);
        } else if i == 7 {
            assert(factorial(7) * 8 == 5040 * 8 == 40320);
            assert(40320 < 0x100000000);
        } else if i == 8 {
            assert(factorial(8) * 9 == 40320 * 9 == 362880);
            assert(362880 < 0x100000000);
        } else if i == 9 {
            assert(factorial(9) * 10 == 362880 * 10 == 3628800);
            assert(3628800 < 0x100000000);
        } else if i == 10 {
            assert(factorial(10) * 11 == 3628800 * 11 == 39916800);
            assert(39916800 < 0x100000000);
        } else if i == 11 {
            assert(factorial(11) * 12 == 39916800 * 12 == 479001600);
            assert(479001600 < 0x100000000);
        } else if i == 12 {
            assert(factorial(12) * 13 == 479001600 * 13 == 6227020800);
            assert(6227020800 >= 0x100000000); // This overflows u32
        }
    }
}

// Helper to prove factorial bounds for the loop invariant
proof fn factorial_bound_up_to_12(i: nat)
    ensures i <= 12 ==> factorial(i) <= 479001600
    decreases i
{
    factorial_values();
    if i == 0 {
        assert(1 <= 479001600);
    } else if i <= 12 {
        if i == 1 {
            assert(1 <= 479001600);
        } else if i == 2 {
            assert(2 <= 479001600);
        } else if i == 3 {
            assert(6 <= 479001600);
        } else if i == 4 {
            assert(24 <= 479001600);
        } else if i == 5 {
            assert(120 <= 479001600);
        } else if i == 6 {
            assert(720 <= 479001600);
        } else if i == 7 {
            assert(5040 <= 479001600);
        } else if i == 8 {
            assert(40320 <= 479001600);
        } else if i == 9 {
            assert(362880 <= 479001600);
        } else if i == 10 {
            assert(3628800 <= 479001600);
        } else if i == 11 {
            assert(39916800 <= 479001600);
        } else if i == 12 {
            assert(479001600 <= 479001600);
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn iterative_factorial(n: u32) -> (result: u32)
    requires n < 13, // prevent overflow
    ensures result == factorial(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut result: u32 = 1;
    let mut i: u32 = 0;
    
    while i < n
        invariant
            i <= n,
            i <= 12,
            n < 13,
            result == factorial(i as nat),
            i <= 12 ==> result <= 479001600,
        decreases n - i,
    {
        i = i + 1;
        proof {
            factorial_step((i - 1) as nat);
            assert(factorial(i as nat) == i * factorial((i - 1) as nat));
            factorial_bound_up_to_12(i as nat);
        }
        result = result * i;
    }
    
    result
}
// </vc-code>

fn main() {}

}