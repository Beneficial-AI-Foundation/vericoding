use vstd::prelude::*;

verus! {

spec fn fact(n: nat) -> nat 
    decreases n
{
    if n == 0 { 1 } else { n * fact((n - 1) as nat) }
}

// <vc-helpers>
proof fn lemma_factorial_recursion(k: nat)
    requires 0 < k
    ensures fact(k) == k * fact((k - 1) as nat)
{
    // This is directly from the definition of fact, no special proof needed.
    // The recursive case covers it.
}

proof fn lemma_fact_is_positive(k: nat)
    ensures fact(k) > 0
    decreases k
{
    if k == 0 {
        assert(fact(0) == 1);
    } else {
        assert(fact(k) == k * fact((k - 1) as nat));
        lemma_fact_is_positive((k - 1) as nat);
        assert(k >= 1 ==> k > 0);
        assert(fact((k - 1) as nat) > 0);
        assert(k * fact((k - 1) as nat) > 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn factorial(n: u32) -> (res: u32)
    requires n <= 12  // to prevent overflow
    ensures res == fact(n as nat)
// </vc-spec>
// <vc-code>
{
    let mut i = 0u32;
    let mut res = 1u32;

    while i < n {
        invariant res as nat == fact(i as nat),
        invariant i <= n,
        invariant fact(i as nat) > 0,
    {
        i = i + 1;
        proof {
            lemma_fact_is_positive(i as nat);
            lemma_factorial_recursion(i as nat); // Use this lemma to prove the invariant holds for the next step.
        }
        res = res * i;
    }}
    res
}
// </vc-code>

fn main() {}

}