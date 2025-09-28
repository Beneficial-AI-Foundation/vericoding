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
/* helper modified by LLM (iteration 5): [fixed incorrect module path for arithmetic lemma] */
proof fn factorial_is_monotonic(i: nat, j: nat)
    requires i <= j
    ensures factorial(i) <= factorial(j)
    decreases j - i
{
    if i < j {
        factorial_is_monotonic(i, (j - 1) as nat);
        assert(j > 0);
        vstd::arithmetic::mul_le_mul_left(factorial((j - 1) as nat), 1, j);
        assert(factorial(j) == j * factorial((j - 1) as nat));
        assert(factorial((j-1) as nat) <= factorial(j));
    }
}

proof fn lemma_factorial_le_u32_max(i: nat)
    requires i < 13
    ensures factorial(i) <= u32::MAX
{
    factorial_is_monotonic(i, 12);
    assert(factorial(12) == 479001600) by(compute);
}
// </vc-helpers>

// <vc-spec>
fn iterative_factorial(n: u32) -> (result: u32)
    requires n < 13,
    ensures result == factorial(n as nat)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): [added assertion to link loop invariant to multiplication] */
{
    let mut result: u32 = 1;
    let mut i: u32 = 1;
    while i <= n
        invariant
            i >= 1,
            i <= n + 1,
            n < 13,
            result as nat == factorial((i - 1) as nat),
        decreases n - i
    {
        proof {
            lemma_factorial_le_u32_max(i as nat);
            assert(factorial(i as nat) == (i as nat) * factorial((i - 1) as nat));
        }
        result = result * i;
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}