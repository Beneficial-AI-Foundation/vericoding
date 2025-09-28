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
proof fn power_succ(a: int, n: nat)
    ensures power(a, n + 1) == a * power(a, n)
{
    assert(power(a, n + 1) == a * power(a, n));
}

proof fn power_nonneg(a: int, n: nat)
    requires a >= 0
    ensures power(a, n) >= 0
    decreases n
{
    if n == 0 {
        assert(power(a, 0) == 1);
    } else {
        power_nonneg(a, n - 1);
        power_succ(a, n - 1);
        assert(power(a, n) == a * power(a, n - 1));
        assert(a >= 0);
        assert(power(a, n - 1) >= 0);
        assert(power(a, n) >= 0);
    }
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
    let n_nat: nat = n as nat;
    let a_int: int = a as int;

    let mut i: nat = 0;
    let mut s_local: int = 1;

    while i < n_nat
        invariant i <= n_nat
        invariant power(a_int, i) == s_local
        decreases n_nat - i
    {
        let old_i = i;
        let old_s = s_local;

        assert(old_s == power(a_int, old_i));

        s_local = old_s * a_int;
        i = old_i + 1;

        proof {
            power_succ(a_int, old_i);
        }

        assert(s_local == power(a_int, i));
    }

    // At exit, i == n_nat and invariant gives s_local == power(a_int, n_nat)
    assert(s_local == power(a_int, n_nat));
    power_nonneg(a_int, n_nat);
    assert(s_local >= 0);

    s_local as u64
}
// </vc-code>

fn main() {}

}