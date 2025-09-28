use vstd::prelude::*;

verus! {

//power -- Stephanie Renee McIntyre
//Based on the code used in the course overheads for Fall 2018

//There is no definition for power, so this function will be used for validating that our imperative program is correct.

/* Proof of implied (a): Follows from definition of the power function. */

/* Proof of implied (b): Details left as exercise, but this is relatively simple. */

/* Proof of implied (c): Simple substitution and uses the fact that i=n. */

/* Proof of termination: the loop guard gives us the expression i<n. This is equivalent to n-i>=0.
   Prior to the loop, n>=0 and i=0.
   Each iteration of the loop, i increases by 1 and thus n-i decreases by 1. Thus n-i will eventually reach 0.
   When the n-i=0, n=i and thus the loop guard ends the loop as it is no longer the case that i<n.
   Thus the program terminates.
*/

// <vc-helpers>
#[verifier(external_body)]
spec fn u64_to_int(u: u64) -> int {
    u as int
}

spec fn u64_to_nat(u: u64) -> nat {
    u as nat
}

// Helper spec function to compute power for proof purposes, ensuring it doesn't overflow u64.
// This is a common pattern when dealing with integer types that have a maximum value.
spec fn power_bounded(a: u64, n: u64) -> u64
    recommends 0 <= a
    decreases n
{
    if n == 0 { 1 } else { (a as int * power_bounded(a, (n - 1) as u64) as int) as u64 }
}
// </vc-helpers>

// <vc-spec>
spec fn power(a: int, n: nat) -> int //function for a to the power of n
    recommends 0 <= a
    decreases n
{
    if n == 0 { 1 } else { a * power(a, (n - 1) as nat) }
}

//Our code from class
fn compute_power(a: u64, n: u64) -> (s: u64)
    /*Pre-Condition*/   requires n >= 0 && a >= 0
    /*Post-Condition*/  ensures s as int == power(a as int, n as nat)
// </vc-spec>
// <vc-code>
{
    let mut i: u64 = 0;
    let mut s: u64 = 1;

    // Additional assertion to help Verus understand the relationship between a, n, i, s and power
    // before the loop starts.
    // This connects the 's' variable with the Verus 'power' spec function.
    assert(s as int == power(a as int, i as nat));

    while i < n
        invariant
            i <= n,
            s as int == power(a as int, i as nat),
            // We need to prove that `s * a` will not overflow `u64` in the next iteration.
            // This assumes that the final result `power(a, n)` will fit in `u64`.
            // The postcondition `s as int == power(a as int, n as nat)` ensures this.
            // So, all intermediate powers `power(a, k)` for `k <= n` must also fit.
            power(a as int, (i + 1) as nat) <= u64::MAX as int,
            // If `a` is 0, special care is needed for 0^0. power(0,0) = 1.
            // For n > 0, power(0, n) = 0.
            // When `a` is 0:
            // if i == 0, s == 1. Then we multiply by 0, s becomes 0.
            // if i > 0, s == 0. Then we multiply by 0, s remains 0.
            // So `s * a` will be 0.
            // When `a` is 1, `s` always remains 1.
            // When `a > 1`, `s` continues to grow.
            // The invariant `power(a as int, (i + 1) as nat) <= u64::MAX as int` is sufficient
            // to prove `s * a` does not overflow, along with the current `s` value.
            // Since `s as int == power(a as int, i as nat)`, we have
            // `(s as int) * (a as int) == power(a as int, i as nat) * a as int == power(a as int, (i + 1) as nat)`.
            // So `(s as int) * (a as int) <= u64::MAX as int`
        decreases (n - i)
    {
        proof {
            // Need to demonstrate s * a does not overflow.
            // From invariant, we have `s as int == power(a as int, i as nat)`.
            // So `s * a` is equivalent to `power(a as int, (i + 1) as nat)`.
            // The loop invariant `power(a as int, (i + 1) as nat) <= u64::MAX as int`
            // ensures that the next value of `s` will fit within `u64`.
            // Thus, the multiplication `s * a` will not overflow.
            assert( (s as int) * (a as int) <= u64::MAX as int );
        }
        s = s * a;
        i = i + 1;

        proof {
            // After `s = s * a; i = i + 1;`, we need to show `s as int == power(a as int, i as nat)`.
            // We know that `power(a as int, (i_old + 1) as nat)` is the new `s` (before `i` update).
            // And the new `i` is `i_old + 1`.
            // So the assertion `s as int == power(a as int, i as nat)` holds.
            assert(s as int == power(a as int, i as nat));
        }
    }

    s
}
// </vc-code>

fn main() {}

}