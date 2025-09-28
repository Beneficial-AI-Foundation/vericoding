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
fn power_succ(x: int, n: nat)
    requires n > 0
    ensures power(x, n) == x * power(x, n - 1)
{
    if n == 0 {
        unreachable!();
    } else {
        // by definition of power
    }
}

fn power_add(x: int, a: nat, b: nat)
    ensures power(x, a + b) == power(x, a) * power(x, b)
    decreases b
{
    if b == 0 {
        // power(x, a + 0) == power(x,a) and power(x,0) == 1
        assert(power(x, a + 0) == power(x, a));
        assert(power(x, 0) == 1);
        assert(power(x, a + 0) == power(x, a) * power(x, 0));
    } else {
        let b1: nat = b - 1;
        // Induction hypothesis
        power_add(x, a, b1);
        // Use succ on b and on a+b to relate
        power_succ(x, b);
        power_succ(x, a + b);
        // From power_succ: power(x, b) == x * power(x, b1)
        assert(power(x, b) == x * power(x, b1));
        // From power_succ: power(x, a + b) == x * power(x, a + b1)
        assert(power(x, a + b) == x * power(x, a + b1));
        // From induction hypothesis: power(x, a + b1) == power(x, a) * power(x, b1)
        assert(power(x, a + b1) == power(x, a) * power(x, b1));
        // Combine to conclude
        assert(power(x, a + b) == power(x, a) * power(x, b));
    }
}

fn power_pow2(x: int, k: nat)
    ensures power(x, 2 * k) == power(x * x, k)
    decreases k
{
    if k == 0 {
        // both sides are 1
        assert(power(x, 0) == 1);
        assert(power(x * x, 0) == 1);
    } else {
        let k1: nat = k - 1;
        // Use induction
        power_pow2(x, k1);
        // power(x, 2*k) = power(x, 2*(k1+1)) = power(x, 2*k1 + 2)
        // By power_add: power(x, 2*k1 + 2) = power(x, 2*k1) * power(x, 2)
        power_add(x, 2 * k1, 2);
        // Show power(x,2) == x * x by two succs
        power_succ(x, 1);
        power_succ(x, 2);
        assert(power(x, 1) == x * power(x, 0));
        assert(power(x, 2) == x * power(x, 1));
        // By induction hypothesis power(x, 2*k1) == power(x*x, k1)
        assert(power(x, 2 * k1) == power(x * x, k1));
        // So power(x, 2*k) == power(x*x,k1) * (x*x) == power(x*x, k1+1)
        assert(power(x, 2 * k) == power(x * x, k1 + 1));
        assert(power(x * x, k1 + 1) == power(x * x, k));
    }
}
// </vc-helpers>

// <vc-spec>
fn power_dc(x: i64, n: u64) -> (p: i64)
    ensures p == power(x as int, n as nat)
// </vc-spec>
// <vc-code>
{
    let mut acc: i64 = 1;
    let mut i: u64 = 0;
    while i < n
        invariant acc as int == power(x as int, i as nat)
        decreases (n - i) as nat
    {
        let old_acc = acc;
        let old_i = i;

        // perform the next multiplication step
        acc = acc * x;
        i = i + 1;

        // Prove the invariant holds after the step
        proof {
            // new_i = old_i + 1
            let new_i: nat = (i) as nat;
            // show new_i > 0 to use power_succ
            assert(new_i > 0);
            // From the loop invariant before the step:
            assert((old_acc as int) == power(x as int, old_i as nat));
            // Use power_succ to relate power(x, new_i) with power(x, old_i)
            power_succ(x as int, new_i);
            // acc == x * old_acc holds by arithmetic
            assert((acc as int) == (x as int) * (old_acc as int));
            // Combine to conclude acc as int == power(x, new_i)
            assert((acc as int) == power(x as int, new_i));
        }
    }

    acc
}
// </vc-code>

fn main() {
    // A few test cases would go here
}

}