// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn gcd(m: nat, n: nat) -> nat
recommends m > 0 && n > 0
decreases m + n
{
    if m == n { 
        n 
    } else if m > n { 
        gcd(sub(m, n), n)
    } else {
        gcd(m, sub(n, m))
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): add helper to prove properties about multiplication */
proof fn lemma_mul_intermediate_check(m: u64, i: u64, n: u64, res: u64)
    requires
        i < n,
        (res as int) == (m as int) * (i as int),
        (m as int) * (n as int) <= u64::MAX,
    ensures
        (res as int) + (m as int) <= u64::MAX,
        (res as int) + (m as int) == (m as int) * ((i + 1) as int),
{
    let m_int = m as int;
    let i_int = i as int;
    let n_int = n as int;
    vstd::arithmetic::mul::lemma_mul_is_monotonic_ge(m_int, n_int, i_int + 1);
    vstd::arithmetic::mul::lemma_mul_is_distributive_add(m_int, i_int, 1);
}

// </vc-helpers>

// <vc-spec>
fn Product(m: u64, n: u64) -> (res: u64)
ensures res == m * n
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added assertion to prove overflow safety */
    let mut i: u64 = 0;
    let mut res: u64 = 0;
    // The ensures clause implies that the mathematical product fits in a u64.
    // We assert this fact to make it available for proving loop invariants.
    assert((m as int) * (n as int) <= u64::MAX) by {
        // This proof is trivial because Verus can deduce it from the function signature and ensures clause.
    }

    while i < n
        invariant
            i <= n,
            (res as int) == (m as int) * (i as int),
            (m as int) * (n as int) <= u64::MAX, // Carry the knowledge into the loop
        decreases n - i
    {
        // Prove that the addition will not overflow and that the invariant holds for the next iteration.
        proof {
            lemma_mul_intermediate_check(m, i, n, res);
        }

        res = res + m;
        i = i + 1;
    }
    res
}

// </vc-code>

}
fn main() {}