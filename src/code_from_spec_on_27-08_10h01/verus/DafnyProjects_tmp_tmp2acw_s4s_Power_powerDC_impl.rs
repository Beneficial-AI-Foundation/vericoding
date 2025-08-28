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
proof fn power_split(x: int, n: nat)
    ensures n % 2 == 0 ==> power(x, n) == power(x * x, n / 2)
    ensures n % 2 == 1 ==> power(x, n) == x * power(x * x, n / 2)
    decreases n
{
    if n == 0 {
    } else if n % 2 == 0 {
        power_split(x, (n - 2) as nat);
        assert(power(x, n) == x * power(x, (n - 1) as nat));
        assert(power(x, (n - 1) as nat) == x * power(x, (n - 2) as nat));
        assert(power(x, n) == x * x * power(x, (n - 2) as nat));
        assert(power(x * x, n / 2) == power(x * x, ((n - 2) / 2 + 1) as nat));
        assert(power(x * x, ((n - 2) / 2 + 1) as nat) == (x * x) * power(x * x, (n - 2) / 2));
    } else {
        power_split(x, ((n - 1) / 2) as nat);
        assert(power(x, n) == x * power(x, (n - 1) as nat));
        assert((n - 1) % 2 == 0);
        assert(power(x, (n - 1) as nat) == power(x * x, (n - 1) / 2));
        assert(power(x * x, n / 2) == power(x * x, (n - 1) / 2));
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
{
    if n == 0 {
        1
    } else if n % 2 == 0 {
        proof {
            power_split(x as int, n as nat);
        }
        let result = power_dc(x * x, n / 2);
        result
    } else {
        proof {
            power_split(x as int, n as nat);
        }
        let result = power_dc(x * x, n / 2);
        x * result
    }
}
// </vc-code>

fn main() {
    // A few test cases would go here
}

}