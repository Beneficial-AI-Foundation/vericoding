// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * power((n - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed incorrect power_of_2 import path */
use vstd::power_of_2::*;

/* helper modified by LLM (iteration 5): kept helper that proves successor relationship */
proof fn lemma_power_successor(i: nat)
    ensures power(i + 1) == 2 * power(i)
{
    reveal(power);
}

/* helper modified by LLM (iteration 5): kept helper to relate spec fn to vstd::pow2 */
proof fn lemma_power_is_pow2(n: nat)
    ensures power(n) == pow2(n)
    decreases n
{
    reveal(power);
    if n > 0 {
        lemma_power_is_pow2(n - 1);
        lemma_pow2_doubles(n - 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn compute_power(n: u32) -> (p: u32)
    requires n < 32,
    ensures p == power(n as nat),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes to logic, which was correct. Relies on fixed helpers. */
    let mut p:u32 = 1;
    let mut i:u32 = 0;
    while i < n
        invariant
            i <= n,
            n < 32,
            p as nat == power(i as nat),
        decreases n - i
    {
        proof {
            let i_nat = i as nat;
            lemma_power_successor(i_nat);
            lemma_power_is_pow2(i_nat + 1);
            lemma_pow2_fits_u32(i_nat + 1);
        }
        p = p * 2;
        i = i + 1;
    }
    p
}
// </vc-code>

}
fn main() {}