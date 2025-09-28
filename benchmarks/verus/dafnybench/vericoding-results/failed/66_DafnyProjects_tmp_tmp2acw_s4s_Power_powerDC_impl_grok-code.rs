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
proof fn lemma_power_double(x: int, k: nat)
    decreases k
    ensures
        power(x, 2 * k) == power(x, k) * power(x, k)
{
    if k == 0 {
        assert(power(x, 0) == 1);
        assert(power(x, 0) * power(x, 0) == 1);
    } else {
        lemma_power_double(x, (k - 1) as nat);
        assert(power(x, 2 * k) == x * power(x, 2 * k - 1));
        assert(power(x, 2 * k - 1) == x * power(x, 2 * (k - 1)));
        assert(power(x, k) == x * power(x, k - 1));
        assert(power(x, 2 * k) == x * x * power(x, 2 * (k - 1)));
        assert(power(x, 2 * (k - 1)) == power(x, (k - 1) as nat) * power(x, (k - 1) as nat)) by(lemma_power_double(x, (k - 1) as nat));
        assert(power(x, 2 * k) == (x * power(x, k - 1)) * (x * power(x, k - 1)));
        assert(power(x, 2 * k) == power(x, k) * power(x, k));
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
        let half_n = n / 2;
        let half_power = power_dc(x, half_n);
        let result = half_power * half_power;
        proof {
            lemma_power_double(x as int, half_n as nat);
            assert(result == power(x as int, n as nat));
        }
        result
    } else {
        let prev_power = power_dc(x, n - 1);
        let result = x * prev_power;
        proof {
            assert(result == power(x as int, n as nat));
        }
        result
    }
}
// </vc-code>

fn main() {
    // A few test cases would go here
}

}