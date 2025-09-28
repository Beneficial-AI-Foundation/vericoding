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
proof fn lemma_power_step(a: int, n: int)
    requires
        n > 0,
    ensures
        power(a, n) == a * power(a, n - 1),
{
    assert(power(a, n) == if n <= 0 { 1 } else { a * power(a, n - 1) });
    assert(power(a, n) == a * power(a, n - 1));
}

proof fn lemma_power_zero(a: int)
    ensures
        power(a, 0) == 1,
{
    assert(power(a, 0) == 1);
}

proof fn lemma_power_succ(a: int, m: int)
    requires
        m >= 0,
    ensures
        power(a, m + 1) == a * power(a, m),
{
    lemma_power_step(a, m + 1);
}
// </vc-helpers>

// <vc-spec>
fn A8Q1(y0: int, x: int) -> (z: int)
    requires y0 >= 0
    ensures z == power(x, y0)
// </vc-spec>
// <vc-code>
{
    let mut i: int = 0;
    let mut acc: int = 1;

    proof { lemma_power_zero(x); }
    assert(acc == power(x, i));

    while i < y0
        invariant
            0 <= i,
            i <= y0,
            acc == power(x, i),
        decreases y0 - i
    {
        let old_i = i;
        assert(old_i >= 0);
        proof { lemma_power_succ(x, old_i); }

        let acc_old = acc;
        acc = x * acc_old;
        i = old_i + 1;

        assert(acc_old == power(x, old_i));
        assert(acc == x * power(x, old_i));
        assert(power(x, old_i + 1) == x * power(x, old_i));
        assert(acc == power(x, old_i + 1));
    }

    assert(i == y0);
    assert(acc == power(x, y0));
    acc
}
// </vc-code>

fn main() {}

}