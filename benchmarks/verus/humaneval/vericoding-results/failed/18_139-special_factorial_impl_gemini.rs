// <vc-preamble>
use vstd::arithmetic::mul::*;
use vstd::prelude::*;

verus! {

spec fn factorial(n: nat) -> (ret:nat)
    decreases n,
{
    if n <= 1 {
        1
    } else {
        n * factorial((n - 1) as nat)
    }
}

spec fn brazilian_factorial(n: nat) -> (ret:nat)
    decreases n,
{
    if n <= 1 {
        factorial(1)
    } else {
        factorial(n) * brazilian_factorial((n - 1) as nat)
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_factorial_is_positive(n: nat)
    ensures factorial(n) >= 1
    decreases n
{
    if n > 1 {
        lemma_factorial_is_positive((n - 1) as nat);
    }
}

/* helper modified by LLM (iteration 3): removed call to non-existent function `mul_ge_one` */
proof fn lemma_brazilian_factorial_is_positive(n: nat)
    ensures brazilian_factorial(n) >= 1
    decreases n
{
    if n > 1 {
        lemma_factorial_is_positive(n);
        lemma_brazilian_factorial_is_positive((n - 1) as nat);
    }
}

/* helper modified by LLM (iteration 3): replaced non-existent `mul_le_mono_left` with `mul_le_mono_nonneg` */
proof fn lemma_brazilian_factorial_is_monotonic(a: nat, b: nat)
    requires a <= b
    ensures brazilian_factorial(a) <= brazilian_factorial(b)
    decreases b - a
{
    if a < b {
        lemma_brazilian_factorial_is_monotonic(a, (b - 1) as nat);
        lemma_factorial_is_positive(b);
        mul_le_mono_nonneg(brazilian_factorial((b - 1) as nat), 1, factorial(b));
    }
}

/* helper modified by LLM (iteration 3): fixed logic and replaced non-existent `mul_le_mono_left` */
proof fn lemma_bf_ge_fact(i: nat, n: nat)
    requires
        1 <= i,
        i <= n,
    ensures brazilian_factorial(n) >= factorial(i)
{
    if i > 1 {
        lemma_brazilian_factorial_is_positive((i - 1) as nat);
        mul_le_mono_nonneg(factorial(i), 1, brazilian_factorial((i - 1) as nat));
    }
    assert(factorial(i) <= brazilian_factorial(i));
    lemma_brazilian_factorial_is_monotonic(i, n);
}

// </vc-helpers>

// <vc-spec>
fn brazilian_factorial_impl(n: u64) -> (ret: Option<u64>)

    ensures
        match ret {
            None => brazilian_factorial(n as nat) > u64::MAX,
            Some(bf) => bf == brazilian_factorial(n as nat),
        },
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): no changes; logic is correct pending helper fixes */
{
    let mut i: u64 = 1;
    let mut current_factorial: u64 = 1;
    let mut bf: u64 = 1;

    while i <= n
        invariant
            1 <= i <= n + 1,
            current_factorial == factorial((i - 1) as nat),
            factorial((i - 1) as nat) <= u64::MAX,
            bf == brazilian_factorial((i - 1) as nat),
            brazilian_factorial((i - 1) as nat) <= u64::MAX,
        decreases n - i
    {
        // 1. Calculate factorial(i)
        let (next_factorial, overflow1) = current_factorial.overflowing_mul(i);
        if overflow1 {
            proof {
                lemma_bf_ge_fact(i as nat, n as nat);
            }
            return None;
        }
        current_factorial = next_factorial;
        
        // 2. Calculate brazilian_factorial(i)
        let (next_bf, overflow2) = bf.overflowing_mul(current_factorial);
        if overflow2 {
            proof {
                lemma_brazilian_factorial_is_monotonic(i as nat, n as nat);
            }
            return None;
        }
        bf = next_bf;

        i = i + 1;
    }

    Some(bf)
}

// </vc-code>

}
fn main() {}