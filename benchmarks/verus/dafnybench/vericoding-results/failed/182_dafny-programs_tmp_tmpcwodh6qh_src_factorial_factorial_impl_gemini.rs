// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn fact(n: nat) -> nat 
    decreases n
{
    if n == 0 { 1 } else { n * fact((n - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): replaced non-existent 'mul_le_mono_left' with 'mul_le_mono_nonneg' */
proof fn lemma_fact_unfold(n: nat)
    requires n > 0
    ensures fact(n) == n * fact((n - 1) as nat)
{
    reveal(fact);
}

proof fn lemma_fact_is_monotonic(m: nat, n: nat)
    requires m <= n
    ensures fact(m) <= fact(n)
    decreases n - m
{
    if m < n {
        lemma_fact_is_monotonic(m, (n - 1) as nat);
        lemma_fact_unfold(n);
        vstd::arithmetic::mul_le_mono_nonneg(1, n as int, fact((n - 1) as nat) as int);
    }
}

proof fn lemma_fact_le_u32_max(n: nat)
    requires n <= 12
    ensures fact(n) <= u32::MAX
{
    lemma_fact_is_monotonic(n, 12);
    assert(fact(12) <= u32::MAX) by(compute);
}
// </vc-helpers>

// <vc-spec>
fn factorial(n: u32) -> (res: u32)
    requires n <= 12
    ensures res == fact(n as nat)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no change necessary, logic is correct */
    let mut i: u32 = 0;
    let mut res: u32 = 1;
    while i < n
        invariant
            n <= 12,
            i <= n,
            res as nat == fact(i as nat),
            fact(i as nat) <= u32::MAX,
        decreases n - i
    {
        proof {
            lemma_fact_le_u32_max((i + 1) as nat);
            lemma_fact_unfold((i + 1) as nat);
        }
        i = i + 1;
        res = res * i;
    }
    res
}
// </vc-code>

}
fn main() {}