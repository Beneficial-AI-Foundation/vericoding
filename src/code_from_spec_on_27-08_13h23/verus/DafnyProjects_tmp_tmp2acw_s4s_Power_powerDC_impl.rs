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
// Helper lemma to prove properties of power for even exponents
proof fn lemma_power_even(x: int, n: nat)
    requires n % 2 == 0,
    ensures power(x, n) == power(x * x, n / 2),
    decreases n
{
    if n == 0 {
        // Base case: n = 0
    } else {
        let n1 = n / 2;
        assert(n == 2 * n1);
        lemma_power_even(x, n1 as nat);
        assert(power(x, n) == x * x * power(x, (n - 2) as nat));
        assert(power(x, (n - 2) as nat) == power(x * x, (n / 2 - 1) as nat));
    }
}

// Helper lemma to establish the base case and inductive steps for power
proof fn lemma_power_properties(x: int, n: nat)
    ensures power(x, 0) == 1,
            n > 0 ==> power(x, n) == x * power(x, (n - 1) as nat),
    decreases n
{
    if n == 0 {
        // Base case handled by definition
    } else {
        // Inductive step handled by definition
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn power_dc(x: i64, n: u64) -> (p: i64)
    ensures p == power(x as int, n as nat)
// </vc-spec>
// </vc-spec>

// <vc-code>
fn power_dc(x: i64, n: u64) -> (p: i64)
    ensures p == power(x as int, n as nat)
    decreases n
{
    if n == 0 {
        1
    } else if n % 2 == 0 {
        let n1 = n / 2;
        proof {
            lemma_power_even(x as int, n as nat);
        }
        let p1 = power_dc(x * x, n1);
        p1
    } else {
        let p1 = power_dc(x, n - 1);
        x * p1
    }
}
// </vc-code>

fn main() {
    // A few test cases would go here
}

}