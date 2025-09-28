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
// Lemma: x^(2n) = (x^2)^n
proof fn lemma_power_even(x: int, n: nat)
    ensures power(x, 2 * n) == power(x * x, n)
    decreases n
{
    if n == 0 {
        // Base case: power(x, 0) == 1 == power(x * x, 0)
        assert(power(x, 0) == 1);
        assert(power(x * x, 0) == 1);
    } else {
        // Inductive case
        lemma_power_even(x, (n - 1) as nat);
        
        // We need to show: power(x, 2*n) == power(x*x, n)
        // First, expand power(x, 2*n)
        assert(2 * n >= 2);
        assert(power(x, 2 * n) == x * power(x, (2 * n - 1) as nat));
        assert((2 * n - 1) as nat == 2 * n - 1);
        assert(power(x, (2 * n - 1) as nat) == x * power(x, (2 * n - 2) as nat));
        assert((2 * n - 2) as nat == 2 * (n - 1) as nat);
        assert(power(x, (2 * (n - 1)) as nat) == power(x * x, (n - 1) as nat)); // by IH
        
        // Now expand power(x*x, n)
        assert(power(x * x, n) == (x * x) * power(x * x, (n - 1) as nat));
        
        // Combining the equations
        assert(power(x, 2 * n) == x * x * power(x, (2 * (n - 1)) as nat));
        assert(power(x, (2 * (n - 1)) as nat) == power(x * x, (n - 1) as nat)); // by IH
        assert(power(x, 2 * n) == x * x * power(x * x, (n - 1) as nat));
        assert(power(x, 2 * n) == power(x * x, n));
    }
}

// Lemma: x^(2n + 1) = x * (x^2)^n
proof fn lemma_power_odd(x: int, n: nat)
    ensures power(x, 2 * n + 1) == x * power(x * x, n)
{
    if n == 0 {
        // Base case: power(x, 1) == x == x * 1 == x * power(x * x, 0)
        assert(power(x, 1) == x * power(x, 0));
        assert(power(x, 1) == x);
        assert(power(x * x, 0) == 1);
    } else {
        // power(x, 2n + 1) = x * power(x, 2n)
        assert(power(x, 2 * n + 1) == x * power(x, (2 * n) as nat));
        
        // By lemma_power_even: power(x, 2n) = power(x * x, n)
        lemma_power_even(x, n);
        assert(power(x, 2 * n) == power(x * x, n));
        assert(power(x, 2 * n + 1) == x * power(x * x, n));
    }
}
// </vc-helpers>

// <vc-spec>
fn power_dc(x: i64, n: u64) -> (p: i64)
    ensures p == power(x as int, n as nat)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        1
    } else if n % 2 == 0 {
        // Even case: x^n = (x^2)^(n/2)
        let n_half = n / 2;
        proof {
            assert(n == 2 * n_half);
            lemma_power_even(x as int, n_half as nat);
            assert(power(x as int, n as nat) == power((x * x) as int, n_half as nat));
        }
        power_dc(x * x, n_half)
    } else {
        // Odd case: x^n = x * (x^2)^((n-1)/2)
        let n_half = (n - 1) / 2;
        proof {
            assert(n == 2 * n_half + 1);
            lemma_power_odd(x as int, n_half as nat);
            assert(power(x as int, n as nat) == (x as int) * power((x * x) as int, n_half as nat));
        }
        x * power_dc(x * x, n_half)
    }
}
// </vc-code>

fn main() {
    // A few test cases would go here
}

}