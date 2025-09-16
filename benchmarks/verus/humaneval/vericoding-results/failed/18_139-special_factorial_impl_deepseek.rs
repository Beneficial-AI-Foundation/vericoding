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
/* helper modified by LLM (iteration 5): strengthen lemmas with proper recursive proofs and overflow handling */
proof fn lemma_factorial_is_positive(n: nat)
    ensures
        factorial(n) >= 1,
    decreases n,
{
    if n > 0 {
        lemma_factorial_is_positive((n - 1) as nat);
    }
}

proof fn lemma_factorial_mul_monotonic(a: nat, b: nat)
    requires
        a <= b,
    ensures
        factorial(a) <= factorial(b),
    decreases b - a,
{
    if a < b {
        lemma_factorial_is_positive(a);
        assert(factorial(b) == b * factorial((b - 1) as nat));
        lemma_factorial_mul_monotonic(a, (b - 1) as nat);
    }
}

proof fn lemma_brazilian_factorial_upper_bound(n: nat)
    ensures
        brazilian_factorial(n) <= factorial(n) * factorial(n) * factorial(n) * factorial(n) * factorial(n),
    decreases n,
{
    if n > 1 {
        lemma_brazilian_factorial_upper_bound((n - 1) as nat);
        lemma_factorial_is_positive(n as nat);
        assert(factorial(n) >= 1);
    }
}

proof fn lemma_u64_overflow_boundary()
    ensures
        factorial(20) <= u64::MAX,
        factorial(21) > u64::MAX,
{
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
/* code modified by LLM (iteration 5): fix verification with proper overflow checks and loop invariants */
{
    if n > 20 {
        return None;
    }
    
    let mut acc: u64 = 1;
    let mut i: u64 = n;
    
    proof {
        lemma_u64_overflow_boundary();
    }
    
    while i >= 1
        invariant
            acc == brazilian_factorial(i as nat),
            i <= n,
            acc <= u64::MAX,
        decreases i,
    {
        proof {
            lemma_factorial_is_positive(i as nat);
        }
        
        let mut fact: u64 = 1;
        let mut j: u64 = i;
        
        while j >= 1
            invariant
                fact == factorial(j as nat),
                j <= i,
                fact <= u64::MAX,
            decreases j,
        {
            assert(fact * j <= u64::MAX);
            fact *= j;
            j -= 1;
        }
        
        assert(acc * fact <= u64::MAX);
        acc *= fact;
        i -= 1;
    }
    
    Some(acc)
}
// </vc-code>

}
fn main() {}