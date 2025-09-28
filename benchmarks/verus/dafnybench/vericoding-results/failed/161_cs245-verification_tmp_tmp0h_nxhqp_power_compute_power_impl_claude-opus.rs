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
proof fn power_mul(a: int, n: nat)
    ensures power(a, n + 1) == a * power(a, n)
    decreases n
{
    // This follows directly from the definition of power
    reveal(power);
}

proof fn power_monotonic(a: int, i: nat, n: nat)
    requires 0 < a
    requires i <= n
    ensures power(a, i) <= power(a, n)
    decreases n - i
{
    if i == n {
        assert(power(a, i) == power(a, n));
    } else {
        reveal(power);
        power_monotonic(a, i + 1, n);
        assert(power(a, i + 1) <= power(a, n));
        assert(power(a, i) <= power(a, i + 1));
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
    let mut s: u64 = 1;
    let mut i: u64 = 0;
    
    // We need to ensure the result won't overflow
    assert(power(a as int, n as nat) <= u64::MAX as int);
    
    while i < n
        invariant
            0 <= i <= n,
            s as int == power(a as int, i as nat),
            power(a as int, n as nat) <= u64::MAX as int,
        decreases n - i,
    {
        let old_s = s;
        let old_i = i;
        
        // Prove that s * a won't overflow
        proof {
            assert(old_s as int == power(a as int, old_i as nat));
            assert(old_i < n);
            power_mul(a as int, old_i as nat);
            assert(power(a as int, (old_i + 1) as nat) == (a as int) * power(a as int, old_i as nat));
            assert(power(a as int, (old_i + 1) as nat) == (a as int) * (old_s as int));
            if a > 0 {
                power_monotonic(a as int, (old_i + 1) as nat, n as nat);
            }
            assert(power(a as int, (old_i + 1) as nat) <= power(a as int, n as nat));
            assert(power(a as int, (old_i + 1) as nat) <= u64::MAX as int);
            assert((a as int) * (old_s as int) <= u64::MAX as int);
        }
        
        // Now multiply s by a and increment i
        s = s * a;
        i = i + 1;
        
        proof {
            assert(s as int == (old_s as int) * (a as int));
            assert(i == old_i + 1);
            assert(s as int == power(a as int, i as nat));
        }
    }
    
    // Post-loop: i == n
    proof {
        assert(i == n);
        assert(s as int == power(a as int, i as nat));
        assert(s as int == power(a as int, n as nat));
    }
    
    s
}
// </vc-code>

fn main() {}

}