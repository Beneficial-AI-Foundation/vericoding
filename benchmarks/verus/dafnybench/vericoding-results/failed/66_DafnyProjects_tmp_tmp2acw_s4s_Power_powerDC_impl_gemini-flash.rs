use vstd::prelude::*;

verus! {

/* 
* Formal verification of an O(log n) algorithm to calculate the natural power of an integer (x^n), 
* illustrating the usage of lemmas and automatic induction in Verus.
* Translated from Dafny to Verus.
*/

// Recursive definition of x^n in functional style, with time and space complexity O(n).
spec fn power(x: int, n: nat) -> int
    decreases n
{
    if n == 0 { 1 } else { x * power(x, (n - 1) as nat) }
}

// Computation of x^n in time and space O(log n).

// <vc-helpers>
#[verifier(nonlinear)]
lemma fn lemma_power_properties()
{
    // Lemma for exponent multiplication: x^(a+b) == x^a * x^b
    assert forall |x: int, a: nat, b: nat| #![auto]
        power(x, (a + b) as nat) == power(x, a) * power(x, b)
    by {
        if b == 0 {
            assert(power(x, (a + 0) as nat) == power(x, a));
            assert(power(x, a) * power(x, 0) == power(x, a) * 1);
        } else {
            assert(power(x, (a + b) as nat) == power(x, a + (b - 1) as nat) * x) by(decreases b);
            assert(power(x, a) * power(x, b) == power(x, a) * (power(x, (b - 1) as nat) * x)) by(decreases b);
            assert(power(x, a + (b - 1) as nat) * x == power(x, a) * (power(x, (b - 1) as nat) * x)) by(decreases b); // Inductive step
        }
    }

    // Lemma for exponent of exponent: (x^a)^b == x^(a*b)
    assert forall |x: int, a: nat, b: nat| #![auto]
        power(power(x, a), b) == power(x, (a * b) as nat)
    by {
        if b == 0 {
            assert(power(power(x, a), 0) == 1);
            assert(power(x, (a * 0) as nat) == power(x, 0) == 1);
        } else {
            assert(power(power(x, a), b) == power(power(x, a), (b - 1) as nat) * power(x, a)) by(decreases b);
            assert(power(x, (a * b) as nat) == power(x, (a * (b - 1)) as nat) * power(x, a)) by(decreases b);
            assert(power(power(x, a), (b - 1) as nat) * power(x, a) == power(x, (a * (b - 1)) as nat) * power(x, a)) by(decreases b); // Inductive step
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn power_dc(x: i64, n: u64) -> (p: i64)
    ensures p == power(x as int, n as nat)
// </vc-spec>
// <vc-code>
{
    // Ensure the helper lemmas are available for use in power_dc
    lemma_power_properties();

    let mut r: i64 = 1;
    let mut b: i64 = x;
    let mut e: u64 = n;

    while e > 0
        invariant
            // Loop invariant: r * b^e == x^n
            r as int * power(b as int, e as nat) == power(x as int, n as nat),
            // Loop invariant: b^e == (original_x)^(2^k * e) for some k (implied by b = x^(2^loop_iterations))
            // The value of 'b' is always 'x' raised to some power of 2
            // And 'e' is 'n' divided by that same power of 2
            e < n + 1 // to avoid overflow issues with e: u64, also implies e decreases
    {
        if e % 2 == 1 {
            // If e is odd, multiply r by b.
            // Old invariant: r_old * b_old^e_old == x^n
            // New state: r_new = r_old * b_old, e_new = e_old - 1
            // We need to show: (r_old * b_old) * b_old^(e_old - 1) == x^n
            // This is r_old * b_old^e_old == x^n, which holds.
            r = r * b;
            e = e - 1; // e is now even
        }
        // Square b and halve e.
        // Old invariant: r_old * b_old^e_old == x^n
        // New state: b_new = b_old^2, e_new = e_old / 2
        // We need to show: r_old * (b_old^2)^(e_old/2) == x^n
        // (b_old^2)^(e_old/2) == b_old^(2 * e_old/2) == b_old^e_old
        // This relies on the lemma (X^a)^b == X^(a*b) which we proved
        b = b * b;
        e = e / 2;
    }
    r
}
// </vc-code>

fn main() {
    // A few test cases would go here
}

}