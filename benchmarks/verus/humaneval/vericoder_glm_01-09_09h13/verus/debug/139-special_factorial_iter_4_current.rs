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
proof fn lemma_fact_zero() {
    assert(factorial(0) == 1);
}

proof fn lemma_fact_succ(i: nat) {
    assert(factorial(i+1) == factorial(i) * (i+1));
}

proof fn lemma_brazilian_fact_rec(n: nat)
    requires
        n >= 1,
    ensures
        brazilian_factorial(n) == factorial(n) * brazilian_factorial(n-1)
{
    if n > 1 {
        // Definition of brazilian_factorial for n>1
    } else {
        // n==1 case
        assert(brazilian_factorial(1) == factorial(1));
        assert(brazilian_factorial(0) == factorial(1));
        assert(factorial(1) * brazilian_factorial(0) == 1);
        assert(brazilian_factorial(1) == 1);
        assert(brazilian_factorial(1) == factorial(1) * brazilian_factorial(0));
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
{
    if n <= 1 {
        Some(1)
    } else {
        let prev = brazilian_factorial_impl(n - 1)?;
        
        let mut fact = 1u64;
        let mut i = 1u64;
        while i < n
            invariant
                i >= 1 && i <= n,
                fact == factorial(i as nat),
                fact <= u64::MAX,
        {
            i = i + 1;
            fact = match fact.checked_mul(i) {
                None => return None,
                Some(x) => x,
            };
        }
        
        proof {
            lemma_brazilian_fact_rec(n as nat);
        }
        
        match fact.checked_mul(prev) {
            None => None,
            Some(result) => Some(result),
        }
    }
}
// </vc-code>

} // verus!
fn main() {}