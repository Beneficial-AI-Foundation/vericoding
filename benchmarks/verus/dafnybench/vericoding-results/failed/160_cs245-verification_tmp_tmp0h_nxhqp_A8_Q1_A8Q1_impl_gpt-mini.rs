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
proof fn lemma_power_succ(a: int, n: int)
    requires n >= 1
    ensures power(a, n) == a * power(a, n - 1)
    decreases n
{
    // Unfolding the definition of power for n > 0 yields the result directly.
    assert(power(a, n) == a * power(a, n - 1));
}
// </vc-helpers>

// <vc-spec>
fn A8Q1(y0: int, x: int) -> (z: int)
    requires y0 >= 0
    ensures z == power(x, y0)
// </vc-spec>
// <vc-code>
{
    let mut i: int = 0.into();
    let mut acc: int = 1.into();
    while i < y0
        invariant 0 <= i && i <= y0 && acc == power(x, i)
        decreases y0 - i
    {
        proof {
            assert(0 <= i);
            assert(i + 1.into() >= 1.into());
            lemma_power_succ(x, i + 1.into());
            assert(acc * x == power(x, i + 1.into()));
        }
        acc = acc * x;
        i = i + 1.into();
    }
    acc
}
// </vc-code>

fn main() {}

}