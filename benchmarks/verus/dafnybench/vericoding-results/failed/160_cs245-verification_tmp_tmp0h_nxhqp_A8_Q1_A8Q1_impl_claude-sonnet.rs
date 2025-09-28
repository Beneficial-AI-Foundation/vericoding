use vstd::prelude::*;

verus! {

// A8Q1 — Steph Renee McIntyre
// Following the solutions from Carmen Bruni

// There is no definition for power, so this function will be used for validating that our imperative program is correct. This is just for Verus.
spec fn power(a: int, n: int) -> int //function for a to the power of n
    recommends 0 <= n
    decreases n when 0 <= n
{
    if n <= 0 { 1 } else { a * power(a, n - 1) }
}

/* Proof of implieds can be seen on LEARN.
    Note: If you are unconvinced, putting asserts for each condition will demonstrate the correctness of the statements. 
*/

// <vc-helpers>
proof fn lemma_power_add(a: int, n: int, m: int)
    requires n >= 0, m >= 0
    ensures power(a, n + m) == power(a, n) * power(a, m)
    decreases n
{
    if n == 0 {
        assert(power(a, 0 + m) == power(a, m));
        assert(power(a, 0) == 1);
        assert(power(a, 0) * power(a, m) == 1 * power(a, m) == power(a, m));
    } else {
        lemma_power_add(a, n - 1, m);
        assert(power(a, (n - 1) + m) == power(a, n - 1) * power(a, m));
        assert(power(a, n + m) == power(a, (n - 1) + 1 + m) == power(a, ((n - 1) + m) + 1));
        assert(power(a, ((n - 1) + m) + 1) == a * power(a, (n - 1) + m));
        assert(a * power(a, (n - 1) + m) == a * (power(a, n - 1) * power(a, m)));
        assert(a * (power(a, n - 1) * power(a, m)) == (a * power(a, n - 1)) * power(a, m));
        assert(a * power(a, n - 1) == power(a, n));
    }
}

proof fn lemma_power_one(a: int)
    ensures power(a, 1) == a
{
    assert(power(a, 1) == a * power(a, 0));
    assert(power(a, 0) == 1);
    assert(a * 1 == a);
}
// </vc-helpers>

// <vc-spec>
fn A8Q1(y0: int, x: int) -> (z: int)
    requires y0 >= 0
    ensures z == power(x, y0)
// </vc-spec>
// <vc-code>
{
    let mut y: int = y0;
    let mut z: int = 1;
    
    while y > 0
        invariant 
            y >= 0,
            z * power(x, y) == power(x, y0)
        decreases y
    {
        proof {
            lemma_power_one(x);
            lemma_power_add(x, 1, y - 1);
        }
        z = z * x;
        y = y - 1;
    }
    
    proof {
        assert(y == 0);
        assert(power(x, 0) == 1);
        assert(z * power(x, y) == z * 1 == z);
        assert(z == power(x, y0));
    }
    
    z
}
// </vc-code>

fn main() {}

}