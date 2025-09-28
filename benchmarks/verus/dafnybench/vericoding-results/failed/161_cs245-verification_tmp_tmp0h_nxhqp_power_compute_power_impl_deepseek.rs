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
proof fn lemma_power_zero(a: int)
    requires
        0 <= a,
    ensures
        power(a, 0) == 1,
{
    reveal(power);
}

proof fn lemma_power_step(a: int, n: nat)
    requires
        0 <= a, n > 0,
    ensures
        power(a, n) == a * power(a, (n - 1) as nat),
{
    reveal(power);
}

proof fn lemma_power_non_decreasing(a: int, n: nat)
    requires
        0 <= a,
    ensures
        power(a, n) >= 0,
    decreases n,
{
    if n > 0 {
        lemma_power_non_decreasing(a, (n - 1) as nat);
    }
}

proof fn lemma_power_monotonic(a: int, i: nat, n: nat)
    requires
        0 <= a, i <= n,
    ensures
        power(a, i) <= power(a, n),
    decreases n - i,
{
    if i < n {
        lemma_power_step(a, (i + 1) as nat);
        lemma_power_monotonic(a, (i + 1) as nat, n);
    }
}

proof fn lemma_mul_bounds(a: u64, b: u64)
    requires
        a >= 0, b >= 0,
    ensures
        a * b >= 0,
{
}

proof fn lemma_no_overflow_mul(a: u64, b: u64)
    requires
        a >= 0, b >= 0, a as int * b as int <= 0xffffffffffffffff,
    ensures
        a * b == (a as int * b as int) as u64,
{
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
    let mut r: u64 = 1;
    assert(r as int == power(a as int, i as nat)) by {
        lemma_power_zero(a as int);
    }
    while i < n
        invariant
            0 <= i <= n,
            r as int == power(a as int, i as nat),
            r >= 1,
        decreases n - i
    {
        let old_i = i;
        let old_r = r;
        proof {
            lemma_power_monotonic(a as int, old_i as nat, n as nat);
            assert(power(a as int, old_i as nat) <= power(a as int, n as nat));
            assert(old_r as int == power(a as int, old_i as nat));
            assert(old_r as int <= power(a as int, n as nat));
            assert(old_r as int * a as int <= power(a as int, n as nat) * a as int);
            lemma_power_step(a as int, (old_i + 1) as nat);
            assert(power(a as int, (old_i + 1) as nat) == a as int * power(a as int, old_i as nat));
            assert(power(a as int, (old_i + 1) as nat) <= power(a as int, n as nat) * a as int);
        }
        assert(old_r * a >= 0) by { lemma_mul_bounds(old_r, a); };
        r = r * a;
        i = i + 1;
        assert(r as int == power(a as int, i as nat)) by {
            lemma_power_step(a as int, i as nat);
            assert(old_r as int == power(a as int, old_i as nat));
            assert(r as int == old_r as int * a as int);
            assert(power(a as int, i as nat) == a as int * power(a as int, old_i as nat));
        }
    }
    assert(i == n);
    r
}
// </vc-code>

fn main() {}

}