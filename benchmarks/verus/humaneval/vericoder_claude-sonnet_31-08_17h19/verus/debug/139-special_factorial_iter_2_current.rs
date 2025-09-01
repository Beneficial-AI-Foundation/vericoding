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
// pure-end
// pure-end

spec fn brazilian_factorial(n: nat) -> (ret:nat)
    decreases n,
{
    if n <= 1 {
        factorial(1)
    } else {
        factorial(n) * brazilian_factorial((n - 1) as nat)
    }
}
// pure-end

// <vc-helpers>
proof fn lemma_factorial_positive(n: nat)
    ensures factorial(n) >= 1
    decreases n
{
    if n <= 1 {
    } else {
        lemma_factorial_positive((n - 1) as nat);
    }
}

proof fn lemma_brazilian_factorial_positive(n: nat)
    ensures brazilian_factorial(n) >= 1
    decreases n
{
    if n <= 1 {
        lemma_factorial_positive(1);
    } else {
        lemma_factorial_positive(n);
        lemma_brazilian_factorial_positive((n - 1) as nat);
    }
}

proof fn lemma_factorial_grows(n: nat)
    requires n >= 1
    ensures factorial(n + 1) >= factorial(n)
    decreases n
{
    lemma_factorial_positive(n);
}

proof fn lemma_brazilian_factorial_grows(n: nat)
    requires n >= 1
    ensures brazilian_factorial(n + 1) >= brazilian_factorial(n)
    decreases n
{
    lemma_factorial_positive(n + 1);
    lemma_brazilian_factorial_positive(n);
}

proof fn lemma_factorial_overflow_bound(n: nat)
    requires n >= 21
    ensures factorial(n) > u64::MAX
    decreases n
{
    if n == 21 {
        assert(factorial(21) > u64::MAX);
    } else {
        lemma_factorial_overflow_bound(21);
        lemma_factorial_positive(n);
    }
}

proof fn lemma_brazilian_factorial_overflow_bound(n: nat)
    requires n >= 14
    ensures brazilian_factorial(n) > u64::MAX
    decreases n
{
    if n == 14 {
        assert(brazilian_factorial(14) > u64::MAX);
    } else {
        lemma_brazilian_factorial_overflow_bound(14);
        lemma_brazilian_factorial_positive(n);
    }
}
// </vc-helpers>

// <vc-spec>
fn brazilian_factorial_impl(n: u64) -> (ret: Option<u64>)
    // post-conditions-start
    ensures
        match ret {
            None => brazilian_factorial(n as nat) > u64::MAX,
            Some(bf) => bf == brazilian_factorial(n as nat),
        },
    // post-conditions-end
// </vc-spec>
// <vc-code>
fn brazilian_factorial_impl(n: u64) -> (ret: Option<u64>)
    decreases n
    // post-conditions-start
    ensures
        match ret {
            None => brazilian_factorial(n as nat) > u64::MAX,
            Some(bf) => bf == brazilian_factorial(n as nat),
        },
    // post-conditions-end
{
    if n >= 14 {
        proof {
            lemma_brazilian_factorial_overflow_bound(n as nat);
        }
        return None;
    }
    
    if n <= 1 {
        return Some(1);
    }
    
    let factorial_n = factorial_impl(n)?;
    let brazilian_factorial_prev = brazilian_factorial_impl(n - 1)?;
    
    match factorial_n.checked_mul(brazilian_factorial_prev) {
        Some(result) => Some(result),
        None => {
            proof {
                lemma_brazilian_factorial_positive(n as nat);
            }
            None
        }
    }
}

fn factorial_impl(n: u64) -> (ret: Option<u64>)
    decreases n
    ensures
        match ret {
            None => factorial(n as nat) > u64::MAX,
            Some(f) => f == factorial(n as nat),
        }
{
    if n >= 21 {
        proof {
            lemma_factorial_overflow_bound(n as nat);
        }
        return None;
    }
    
    if n <= 1 {
        return Some(1);
    }
    
    let prev = factorial_impl(n - 1)?;
    
    match n.checked_mul(prev) {
        Some(result) => Some(result),
        None => {
            proof {
                lemma_factorial_positive(n as nat);
            }
            None
        }
    }
}
// </vc-code>

} // verus!
fn main() {}