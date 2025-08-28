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
proof fn power_positive(a: int, n: int)
    requires 0 <= n
    ensures power(a, n) == if n == 0 { 1 } else { a * power(a, n - 1) }
{
}

proof fn power_zero(a: int)
    ensures power(a, 0) == 1
{
}

proof fn power_one(a: int)
    ensures power(a, 1) == a
{
}

proof fn power_mul(a: int, m: int, n: int)
    requires 0 <= m, 0 <= n
    ensures power(a, m + n) == power(a, m) * power(a, n)
    decreases m + n
{
    if m == 0 {
        assert(power(a, m + n) == power(a, n));
        assert(power(a, m) == 1);
    } else if n == 0 {
        assert(power(a, m + n) == power(a, m));
        assert(power(a, n) == 1);
    } else {
        power_mul(a, m - 1, n);
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn A8Q1(y0: int, x: int) -> (z: int)
    requires y0 >= 0
    ensures z == power(x, y0)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    let mut y = y0;
    let mut z = 1;
    
    while y > 0
        invariant 0 <= y <= y0
        invariant z * power(x, y) == power(x, y0)
        decreases y
    {
        z = z * x;
        y = y - 1;
    }
    
    z
}
// </vc-code>

fn main() {}

}