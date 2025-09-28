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
proof fn lemma_power_mult(a: int, n: nat, m: nat)
    requires
        0 <= a,
    decreases n
    ensures
        power(a, n) * power(a, m) == power(a, n + m)
{
    if n == 0 {
        assert(power(a, n) == 1);
        assert(power(a, m) == power(a, 0 + m));
    } else {
        lemma_power_mult(a, (n - 1) as nat, m);
        assert(power(a, n) == a * power(a, (n - 1) as nat));
        assert(power(a, n) * power(a, m) == a * power(a, (n - 1) as nat) * power(a, m));
        assert(a * power(a, (n - 1) as nat) * power(a, m) == a * (power(a, (n - 1) as nat + m)));
        assert(a * (power(a, (n - 1) as nat + m)) == power(a, n + m));
    }
}

proof fn lemma_power_adds(a: int, n: nat, m: nat)
    requires
        0 <= a,
    ensures
        power(a, n + m) == power(a, n) * power(a, m)
{
    lemma_power_mult(a, n, m);
}

proof fn lemma_power_one(a: int)
    requires
        0 <= a,
    ensures
        power(a, 1) == a
{
    assert(power(a, 1) == a * power(a, 0));
    assert(power(a, 0) == 1);
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

    proof {
        assert(power(a as int, n as nat) == power(a as int, 0 + n as nat));
        lemma_power_adds(a as int, 0, n as nat);
        assert(power(a as int, n as nat) == power(a as int, 0) * power(a as int, n as nat));
        assert(power(a as int, 0) == 1);
        assert(s as int == power(a as int, i as nat));
    }

    while i < n
        invariant
            0 <= i <= n,
            s as int == power(a as int, i as nat),
            a as int >= 0,
    {
        let old_i = i;
        let old_s = s;
        
        i = i + 1;
        s = s * a;

        proof {
            assert(old_i < n);
            assert(old_i as int + 1 == i as int);
            lemma_power_adds(a as int, old_i as nat, 1);
            assert(power(a as int, i as nat) == power(a as int, old_i as nat) * power(a as int, 1));
            lemma_power_one(a as int);
            assert(power(a as int, 1) == a as int);
            assert(power(a as int, i as nat) == old_s as int * a as int);
            assert(s as int == old_s as int * a as int);
            assert(s as int == power(a as int, i as nat));
        }
    }

    assert(i == n);
    s
}
// </vc-code>

fn main() {}

}