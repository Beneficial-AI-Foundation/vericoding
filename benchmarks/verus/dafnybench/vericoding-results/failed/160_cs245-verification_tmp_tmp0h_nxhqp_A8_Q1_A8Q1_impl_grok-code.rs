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
// <vc-helpers>
// A8Q1 — Steph Renee McIntyre
// Following the solutions from Carmen Bruni

/* Proof of implieds can be seen on LEARN.
    Note: If you are unconvinced, putting asserts for each condition will demonstrate the correctness of the statements. 
*/
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn A8Q1(y0: int, x: int) -> (z: int)
    requires y0 >= 0
    ensures z == power(x, y0)
// </vc-spec>
// <vc-code>
{
    let mut res: int = 1;
    let mut y: int = y0;
    assert(y >= 0);
    while y > 0
        invariant(y >= 0)
        invariant(res * power(x, y) == power(x, y0))
        decreases(y when y >= 0)
    {
        res = res * x;
        y = y - 1;
        assert(y >= 0);
    }
    res
}
// </vc-code>

fn main() {}

}