// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed call to non-existent function */
proof fn lemma_factorial_is_positive(n: nat)
    ensures factorial(n) >= 1
    decreases n
{
    if n > 0 {
        lemma_factorial_is_positive((n-1) as nat);
    }
}

/* helper modified by LLM (iteration 5): fixed call to non-existent function */
proof fn lemma_factorial_monotonic(i: nat, j: nat)
    requires i <= j
    ensures factorial(i) <= factorial(j)
    decreases j - i
{
    if i < j {
        lemma_factorial_monotonic(i, (j - 1) as nat);
        lemma_factorial_is_positive((j - 1) as nat);
        if j > 1 {
             vstd::arithmetic::mult_is_monotonic(1, j as int, factorial((j-1) as nat) as int);
        }
        assert(factorial((j - 1) as nat) <= factorial(j));
    }
}
// </vc-helpers>

// <vc-spec>
fn compute_factorial(n: i32) -> (u: i32)
    requires 1 <= n,
    ensures u == factorial(n as nat),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes, as primary error was compilation in helpers */
    let mut u: i32 = 1;
    let mut i: i32 = 2;

    proof {
        assert(factorial(1) == 1 * factorial(0));
        assert(factorial(1) == 1);
    }

    while i <= n
        invariant
            2 <= i <= n + 1,
            u > 0,
            u as nat == factorial((i - 1) as nat),
            factorial(i as nat) <= i32::MAX,
        decreases n - i
    {
        proof {
            assert(factorial(i as nat) == (i as nat) * factorial((i - 1) as nat));
        }
        u = u * i;
        i = i + 1;
    }
    u
}
// </vc-code>

}
fn main() {}