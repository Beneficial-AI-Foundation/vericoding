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
proof fn power_step(a: int, n: nat)
    requires 0 <= a
    ensures power(a, n + 1) == a * power(a, n)
    decreases n
{
    reveal(power);
    assert(n + 1 != 0);
    assert(((n + 1) - 1) as nat == n);
    assert(power(a, n + 1) == a * power(a, ((n + 1) - 1) as nat));
    assert(power(a, n + 1) == a * power(a, n));
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
    let mut s: u64 = 1;
    let mut i: u64 = 0;
    while i < n
        invariant
            i <= n,
            s as int == power(a as int, i as nat)
        decreases (n - i) as int
    {
        let old_i = i;
        let old_s = s;

        s = s * a;
        i = i + 1;

        proof {
            assert(old_s as int == power(a as int, old_i as nat));
            assert(i == old_i + 1);
            assert((i as nat) == (old_i as nat) + 1);

            power_step(a as int, old_i as nat);
            assert(power(a as int, (old_i as nat) + 1) == (a as int) * power(a as int, old_i as nat));

            assert(s as int == (old_s as int) * (a as int));
            assert((old_s as int) * (a as int) == (a as int) * (old_s as int));
            assert(s as int == power(a as int, i as nat));
        }
    }
    s
// </vc-code>

fn main() {}

}