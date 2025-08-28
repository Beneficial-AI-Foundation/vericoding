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

proof fn power_base(a: int)
    ensures power(a, 0) == 1
{
}

proof fn power_monotonic(a: int, i: nat, n: nat)
    requires i <= n && a >= 0
    ensures power(a, i) * power(a, (n - i) as nat) == power(a, n)
    decreases n - i
{
    if i == n {
        power_base(a);
        assert(power(a, (n - i) as nat) == power(a, 0));
        assert(power(a, 0) == 1);
        assert(power(a, i) * 1 == power(a, i));
    } else {
        power_monotonic(a, i + 1, n);
        power_step(a, (n - i) as nat);
        assert(power(a, (n - i) as nat) == a * power(a, (n - i - 1) as nat));
        power_step(a, (i + 1) as nat);
        assert(power(a, (i + 1) as nat) == a * power(a, i as nat));
        assert(power(a, i) * power(a, (n - i) as nat) == power(a, i) * a * power(a, (n - i - 1) as nat));
        assert(a * power(a, i) == power(a, (i + 1) as nat));
        assert(power(a, i) * a * power(a, (n - i - 1) as nat) == power(a, (i + 1) as nat) * power(a, (n - i - 1) as nat));
    }
}

proof fn power_bounded_step(a: u64, i: u64, n: u64)
    requires 
        i < n,
        a >= 1,
        power(a as int, n as nat) <= u64::MAX,
        power(a as int, i as nat) <= u64::MAX
    ensures (a as int) * power(a as int, i as nat) <= u64::MAX
{
    power_step(a as int, (i + 1) as nat);
    assert(power(a as int, (i + 1) as nat) == (a as int) * power(a as int, i as nat));
    
    if i + 1 <= n {
        power_monotonic(a as int, (i + 1) as nat, n as nat);
        assert(power(a as int, (i + 1) as nat) <= power(a as int, n as nat));
        assert((a as int) * power(a as int, i as nat) <= u64::MAX);
    }
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
    let mut s: u64 = 1;
    let mut i: u64 = 0;
    
    proof {
        power_base(a as int);
        assert(power(a as int, 0) == 1);
        assert(s as int == power(a as int, i as nat));
    }
    
    while i < n
        invariant 
            0 <= i <= n,
            s as int == power(a as int, i as nat),
            s <= u64::MAX,
            a >= 1,
            power(a as int, n as nat) <= u64::MAX
        decreases n - i
    {
        proof {
            power_bounded_step(a, i, n);
            power_step(a as int, (i + 1) as nat);
            assert(power(a as int, (i + 1) as nat) == (a as int) * power(a as int, i as nat));
            assert(s as int == power(a as int, i as nat));
            assert((s * a) as int == (s as int) * (a as int));
            assert((s * a) as int == power(a as int, (i + 1) as nat));
            assert((s * a) as int <= u64::MAX);
            assert(s * a <= u64::MAX);
        }
        s = s * a;
        i = i + 1;
    }
    
    proof {
        assert(i == n);
        assert(s as int == power(a as int, n as nat));
    }
    
    s
}
// </vc-code>

fn main() {}

}