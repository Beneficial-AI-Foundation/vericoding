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
proof fn power_step(x: int, n: int)
    requires n >= 0
    ensures power(x, n + 1) == x * power(x, n)
{
    reveal(power);
}
// </vc-helpers>

// <vc-spec>
fn A8Q1(y0: int, x: int) -> (z: int)
    requires y0 >= 0
    ensures z == power(x, y0)
// </vc-spec>
// <vc-code>
{
    let mut z = 1;
    let mut i = 0;
    while (i < y0)
        invariant (0 <= i <= y0)
        invariant (z == power(x, i))
        decreases (y0 - i)
    {
        z = z * x;
        i = i + 1;
        proof {
            power_step(x, i - 1);
            assert(z == power(x, i));
        }
    }
    z
}
// </vc-code>

fn main() {}

}