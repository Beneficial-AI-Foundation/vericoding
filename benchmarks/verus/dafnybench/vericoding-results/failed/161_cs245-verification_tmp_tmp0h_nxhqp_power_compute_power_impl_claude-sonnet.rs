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
    requires n > 0
    ensures power(a, n) == a * power(a, (n - 1) as nat)
{
}

proof fn power_zero(a: int)
    ensures power(a, 0) == 1
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
    let mut s: u64 = 1;
    let mut i: u64 = 0;
    
    while i < n
        invariant 
            0 <= i <= n,
            s as int == power(a as int, i as nat),
            s <= u64::MAX / a || i == n
        decreases n - i
    {
        i = i + 1;
        proof {
            power_step(a as int, i as nat);
        }
        s = s * a;
    }
    
    s
}
// </vc-code>

fn main() {}

}