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
proof fn lemma_factorial_positive(n: nat)
    ensures factorial(n) > 0
    decreases n
{
    if n <= 1 {
        assert(factorial(n) == 1);
    } else {
        lemma_factorial_positive((n - 1) as nat);
        assert(factorial((n - 1) as nat) > 0);
        assert(factorial(n) == n * factorial((n - 1) as nat));
        assert(n > 0);
        assert(factorial(n) > 0);
    }
}

proof fn lemma_brazilian_factorial_positive(n: nat)
    ensures brazilian_factorial(n) > 0
    decreases n
{
    if n <= 1 {
        assert(brazilian_factorial(n) == factorial(1));
        assert(factorial(1) == 1);
        assert(brazilian_factorial(n) == 1);
    } else {
        lemma_factorial_positive(n);
        lemma_brazilian_factorial_positive((n - 1) as nat);
        assert(factorial(n) > 0);
        assert(brazilian_factorial((n - 1) as nat) > 0);
        assert(brazilian_factorial(n) == factorial(n) * brazilian_factorial((n - 1) as nat));
        assert(brazilian_factorial(n) > 0);
    }
}

/* helper modified by LLM (iteration 5): fixed monotonicity lemmas */
proof fn lemma_factorial_monotonic(a: nat, b: nat)
    requires a <= b
    ensures factorial(a) <= factorial(b)
    decreases b - a
{
    if a == b {
        assert(factorial(a) == factorial(b));
    } else {
        lemma_factorial_monotonic(a, (b - 1) as nat);
        lemma_factorial_positive((b - 1) as nat);
        assert(factorial(b) == b * factorial((b - 1) as nat));
        assert(b >= 1);
        assert(factorial((b - 1) as nat) > 0);
        assert(factorial(a) <= factorial((b - 1) as nat));
        assert(factorial(b) >= factorial((b - 1) as nat));
        assert(factorial(a) <= factorial(b));
    }
}

proof fn lemma_brazilian_factorial_monotonic(a: nat, b: nat)
    requires a <= b
    ensures brazilian_factorial(a) <= brazilian_factorial(b)
    decreases b - a
{
    if a == b {
        assert(brazilian_factorial(a) == brazilian_factorial(b));
    } else if b == 0 {
        assert(a == 0);
    } else {
        lemma_brazilian_factorial_monotonic(a, (b - 1) as nat);
        lemma_factorial_positive(b);
        lemma_brazilian_factorial_positive((b - 1) as nat);
        assert(brazilian_factorial(b) == factorial(b) * brazilian_factorial((b - 1) as nat));
        assert(factorial(b) > 0);
        assert(brazilian_factorial((b - 1) as nat) > 0);
        assert(brazilian_factorial(a) <= brazilian_factorial((b - 1) as nat));
        assert(brazilian_factorial(b) >= brazilian_factorial((b - 1) as nat));
        assert(brazilian_factorial(a) <= brazilian_factorial(b));
    }
}

proof fn lemma_brazilian_factorial_ge_factorial(n: nat)
    ensures brazilian_factorial(n) >= factorial(n)
    decreases n
{
    if n <= 1 {
        assert(brazilian_factorial(n) == factorial(1));
        assert(factorial(1) == 1);
        assert(factorial(n) == 1);
    } else {
        lemma_brazilian_factorial_ge_factorial((n - 1) as nat);
        lemma_factorial_positive((n - 1) as nat);
        lemma_brazilian_factorial_positive((n - 1) as nat);
        assert(brazilian_factorial(n) == factorial(n) * brazilian_factorial((n - 1) as nat));
        assert(brazilian_factorial((n - 1) as nat) >= factorial((n - 1) as nat));
        assert(brazilian_factorial((n - 1) as nat) >= 1);
        assert(factorial((n - 1) as nat) > 0);
        assert(brazilian_factorial(n) >= factorial(n) * 1);
        assert(brazilian_factorial(n) >= factorial(n));
    }
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
{
    /* code modified by LLM (iteration 5): fixed precondition errors */
    if n == 0 {
        return Some(1);
    }
    if n == 1 {
        return Some(1);
    }
    
    let mut result: u64 = 1;
    let mut i: u64 = 1;
    
    while i <= n
        invariant
            1 <= i,
            i <= n + 1,
            result == brazilian_factorial((i - 1) as nat),
        decreases n - i + 1
    {
        let mut fact: u64 = 1;
        let mut j: u64 = 1;
        
        while j <= i
            invariant
                1 <= j,
                j <= i + 1,
                fact == factorial((j - 1) as nat),
            decreases i - j + 1
        {
            if let Some(new_fact) = fact.checked_mul(j) {
                fact = new_fact;
            } else {
                proof {
                    lemma_factorial_positive((j - 1) as nat);
                    lemma_factorial_positive(j as nat);
                    assert(factorial(j as nat) == j * factorial((j - 1) as nat));
                    assert(factorial(j as nat) > u64::MAX);
                    lemma_brazilian_factorial_positive(i as nat);
                    lemma_brazilian_factorial_ge_factorial(i as nat);
                    if j <= i {
                        lemma_factorial_monotonic(j as nat, i as nat);
                    }
                    if i <= n {
                        lemma_brazilian_factorial_monotonic(i as nat, n as nat);
                    }
                }
                return None;
            }
            if j < i {
                j = j + 1;
            } else {
                j = j + 1;
            }
        }
        
        assert(fact == factorial(i as nat));
        
        if let Some(new_result) = result.checked_mul(fact) {
            result = new_result;
        } else {
            proof {
                lemma_factorial_positive(i as nat);
                lemma_brazilian_factorial_positive((i - 1) as nat);
                assert(brazilian_factorial(i as nat) == factorial(i as nat) * brazilian_factorial((i - 1) as nat));
                assert(brazilian_factorial(i as nat) > u64::MAX);
                if i <= n {
                    lemma_brazilian_factorial_monotonic(i as nat, n as nat);
                }
            }
            return None;
        }
        
        assert(result == brazilian_factorial(i as nat));
        i = i + 1;
    }
    
    assert(i == n + 1);
    assert(result == brazilian_factorial(n as nat));
    Some(result)
}
// </vc-code>

}
fn main() {}