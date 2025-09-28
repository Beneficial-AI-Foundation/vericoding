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
#[verifier(external_body)]
proof fn u32_to_nat(n: u32) -> (res: nat)
    ensures res == n as nat
{
    n as nat
}
// </vc-helpers>

// <vc-spec>
fn iterative_factorial(n: u32) -> (result: u32)
    requires n < 13, // prevent overflow
    ensures result == factorial(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut i: u32 = 0;
    let mut acc: u32 = 1;

    // The loop computes the factorial iteratively.
    // The loop invariant ensures that 'acc' holds the factorial of 'i' at each iteration.
    // The decrease clause ensures loop termination.
    while i < n
        invariant
            // 'i' is always less than or equal to 'n'.
            i <= n,
            // 'acc' stores the factorial of 'i'.
            acc as nat == factorial(i as nat),
            // The multiplication acc * (i + 1) will not overflow a u32.
            // This is ensured by the precondition n < 13, which means factorial(n) <= factorial(12) = 479,001,600, which fits in u32.
            (acc as u64) * ((i + 1) as u64) <= 0x1_0000_0000u64,
        decreases (n - i)
    {
        i = i + 1;
        // Proof that the next value of `acc` still satisfies the invariant
        // `acc as nat == factorial(i as nat)` after `i` is incremented.
        proof {
            // Before the update: old_acc == factorial(old_i)
            // After the update: new_i == old_i + 1
            // We want to show: old_acc * new_i == factorial(new_i)
            // This is equivalent to: factorial(old_i) * (old_i + 1) == factorial(old_i + 1)
            // This is true by the definition of factorial.
            assert(acc as nat * (i as nat) == factorial(i as nat));
        }
        acc = acc * i;
    }
    // After the loop, `i` is equal to `n`.
    // The invariant `acc as nat == factorial(i as nat)` becomes `acc as nat == factorial(n as nat)`.
    acc
}
// </vc-code>

fn main() {}

}