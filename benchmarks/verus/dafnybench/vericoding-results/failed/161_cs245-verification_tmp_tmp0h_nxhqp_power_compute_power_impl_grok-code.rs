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
proof fn power_induct(a: int, n: nat)
    requires 0 <= a
    decreases n
    ensures power(a, n) == if n == 0 { 1 } else { a * power(a, (n - 1) as nat) }
{
    if n != 0 {
        power_induct(a, (n - 1) as nat);
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
    let mut i: u64 = 0;
    let mut res: int = 1;
    while i < n
        invariant
            i <= n,
            res == power(a as int, i as nat)
        decreases n - i
    {
        proof {
            assert(res == power(a as int, i as nat));
            power_induct(a as int, (i + 1) as nat);
            assert(power(a as int, (i + 1) as nat) == power(a as int, i as nat) * (a as int));
        }
        res = res * (a as int);
        i = i + 1;
        assert(res == power(a as int, i as nat));
    }
    return res as u64;
}
// </vc-code>

fn main() {}

}