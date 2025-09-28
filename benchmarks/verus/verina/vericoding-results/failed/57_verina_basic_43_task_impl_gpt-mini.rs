// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): induction lemma for one step of the summation */
proof fn lemma_step(m: nat, res: nat)
    requires
        15 * res == m * (2 * m + 1) * (7 + 24 * (m * m * m) - 12 * (m * m) - 14 * m)
    ensures
        15 * (res + (2 * m + 1) * (2 * m + 1) * (2 * m + 1) * (2 * m + 1)) ==
        (m + 1) * (2 * (m + 1) + 1) * (7 + 24 * ((m + 1) * (m + 1) * (m + 1)) - 12 * ((m + 1) * (m + 1)) - 14 * (m + 1))
{
    proof {
        let lhs = 15 * (res + (2 * m + 1) * (2 * m + 1) * (2 * m + 1) * (2 * m + 1));
        assert(lhs == m * (2 * m + 1) * (7 + 24 * m * m * m - 12 * m * m - 14 * m) + 15 * (2 * m + 1) * (2 * m + 1) * (2 * m + 1) * (2 * m + 1));
        let mid = 48 * m * m * m * m * m + 240 * m * m * m * m + 440 * m * m * m + 360 * m * m + 127 * m + 15;
        assert(m * (2 * m + 1) * (7 + 24 * m * m * m - 12 * m * m - 14 * m) + 15 * (2 * m + 1) * (2 * m + 1) * (2 * m + 1) * (2 * m + 1) == mid);
        let rhs = (m + 1) * (2 * (m + 1) + 1) * (7 + 24 * (m + 1) * (m + 1) * (m + 1) - 12 * (m + 1) * (m + 1) - 14 * (m + 1));
        assert(rhs == mid);
        assert(lhs == rhs);
    }
}

// </vc-helpers>

// <vc-spec>
fn sum_of_fourth_power_of_odd_numbers(n: nat) -> (result: nat)
    ensures
        15 * result == n * (2 * n + 1) * (7 + 24 * (n * n * n) - 12 * (n * n) - 14 * n)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterative summation using int loop variables with casts to nat for specs and lemma calls */
    let mut m: int = 0;
    let mut res: int = 0;
    let nn: int = n as int;
    while m < nn
        invariant
            15 * (res as nat) == (m as nat) * (2 * (m as nat) + 1) * (7 + 24 * ((m as nat) * (m as nat) * (m as nat)) - 12 * ((m as nat) * (m as nat)) - 14 * (m as nat)),
            m >= 0,
            res >= 0,
            (m as nat) <= n,
        decreases nn - m
    {
        let prev = res;
        let odd = 2 * m + 1;
        let add = odd * odd * odd * odd;
        res = prev + add;
        proof { lemma_step(m as nat, prev as nat); }
        m = m + 1;
    }
    res as nat
}

// </vc-code>

}
fn main() {}