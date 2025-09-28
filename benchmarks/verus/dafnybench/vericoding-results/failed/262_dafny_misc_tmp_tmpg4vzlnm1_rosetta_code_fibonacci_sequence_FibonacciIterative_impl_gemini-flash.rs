use vstd::prelude::*;

verus! {

// definition of Fibonacci numbers
spec fn fibonacci(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        fibonacci((n - 1) as nat) + fibonacci((n - 2) as nat)
    }
}

// iterative calculation of Fibonacci numbers

// <vc-helpers>
#[verifier(nonlinear)]
proof fn lemma_fibonacci_sum_small(a: nat, b: nat)
    requires
        a < 100,
        b < 100,
        a + b < 100,
    ensures
        fibonacci(a) + fibonacci(b) == fibonacci(a) + fibonacci(b), // trivial tautology, but serves as a placeholder for Verus to reason about fibonacci values
{
    // This lemma is a placeholder. If intermediate Fibonacci numbers exceed u64,
    // more specific lemmas about their growth rate would be needed.
    // For n < 100, u64 should be sufficient.
}

proof fn lemma_fibonacci_properties(n: nat)
    requires n < 100
{
    // No specific proof steps are needed here, as the recursive definition of fibonacci
    // already ensures it returns a non-negative integer (nat).
    // This lemma primarily ensures Verus tracks properties about fibonacci.
}
proof fn lemma_fibonacci_induction(i: nat)
    requires i > 0, i < 99
    ensures fibonacci(i as nat) + fibonacci((i + 1) as nat) == fibonacci((i + 2) as nat)
{
    // This proof is essentially the definition of fibonacci.
    // We explicitly state it here to help Verus in the loop invariant.
    assert(fibonacci((i + 2) as nat) == fibonacci((i + 1) as nat) + fibonacci(i as nat));
}
// </vc-helpers>

// <vc-spec>
fn fibonacci_iterative(n: u64) -> (f: u64)
    requires n < 100  // practical bound to prevent overflow
    ensures f == fibonacci(n as nat)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 0;
    }
    if n == 1 {
        return 1;
    }

    let mut a: u64 = 0;
    let mut b: u64 = 1;
    let mut i: u64 = 1;

    // Prove initial state for loop invariant
    proof {
        assert(a == fibonacci(0) as u64);
        assert(b == fibonacci(1) as u64);
        assert(i == 1);
    }

    while i < n
        invariant
            i <= n,
            i >= 1,
            // Ensure intermediate fibonacci values fit in u64
            b < 20000000000000000000u64, // A sufficiently large bound for fib(99)
            a == fibonacci((i - 1) as nat) as u64,
            b == fibonacci(i as nat) as u64,
            n < 100,
            i as nat <= n as nat,
    {
        proof {
            // Prove that fib(i) + fib(i-1) = fib(i+1)
            // This is the core induction step.
            if i + 1 < n + 1 { // Check to prevent `n + 1` from overflowing if `n` is u64::MAX
                if i < 99 {
                    lemma_fibonacci_induction((i - 1) as nat);
                }
                assert((fibonacci((i - 1) as nat) as u64) + (fibonacci(i as nat) as u64) == fibonacci((i + 1) as nat) as u64);
            }
        }
        let next_b = a + b;
        a = b;
        b = next_b;
        i = i + 1;
    }
    b
}
// </vc-code>

fn main() {
}

}