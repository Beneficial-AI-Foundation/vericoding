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
proof fn power_even(x: int, k: nat)
    ensures power(x, 2 * k) == power(x, k) * power(x, k)
{
    if k == 0 {
        assert(power(x, 0) == 1);
        assert(power(x, 0) * power(x, 0) == 1);
    } else {
        let k_prev = k - 1;
        power_even(x, k_prev as nat);
        assert(power(x, 2 * k) == x * power(x, (2 * k - 1) as nat));
        assert(power(x, (2 * k - 1) as nat) == x * power(x, (2 * k - 2) as nat));
        assert(power(x, 2 * k) == x * x * power(x, (2 * k - 2) as nat));
        assert(2 * k - 2 == 2 * k_prev);
        assert(power(x, 2 * k) == x * x * power(x, (2 * k_prev) as nat));
        assert(power(x, (2 * k_prev) as nat) == power(x, k_prev as nat) * power(x, k_prev as nat));
        assert(power(x, 2 * k) == x * x * (power(x, k_prev as nat) * power(x, k_prev as nat)));
        assert(power(x, k) == x * power(x, k_prev as nat));
        assert(power(x, k) * power(x, k) == (x * power(x, k_prev as nat)) * (x * power(x, k_prev as nat)));
        assert(power(x, k) * power(x, k) == x * x * (power(x, k_prev as nat) * power(x, k_prev as nat)));
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
        let k = n / 2;
        let y = power_dc(x, k);
        proof {
            let x_int = x as int;
            let k_nat = k as nat;
            power_even(x_int, k_nat);
            assert(y == power(x_int, k_nat));
            assert(n == 2 * k);
            assert((n as nat) == 2 * k_nat);
            assert(power(x_int, (n as nat)) == power(x_int, 2 * k_nat));
            assert(power(x_int, 2 * k_nat) == power(x_int, k_nat) * power(x_int, k_nat));
            assert(power(x_int, (n as nat)) == y * y);
        }
        y * y
    } else {
        let k = (n - 1) / 2;
        let y = power_dc(x, k);
        proof {
            let x_int = x as int;
            let k_nat = k as nat;
            power_even(x_int, k_nat);
            assert(y == power(x_int, k_nat));
            assert(2 * k + 1 == n);
            assert((n as nat) == 2 * k_nat + 1);
            assert(power(x_int, 2 * k_nat) == power(x_int, k_nat) * power(x_int, k_nat));
            assert(power(x_int, (2 * k_nat + 1) as nat) == x_int * power(x_int, 2 * k_nat));
            assert(power(x_int, (n as nat)) == power(x_int, (2 * k_nat + 1) as nat));
            assert(power(x_int, (n as nat)) == x_int * (y * y));
        }
        x * y * y
    }
}
// </vc-code>

fn main() {
    // A few test cases would go here
}

}