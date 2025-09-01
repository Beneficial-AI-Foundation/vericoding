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
lemma factorial_step(k: nat)
    requires k >= 1
    ensures factorial(k) == factorial(k-1) * k
    #[trigger(factorial(k))]
    #[trigger(factorial(k-1))]
{
    if k == 1 {
        assert(factorial(1) == factorial(0) * 1);
    } else {
        assert(factorial(k) == k * factorial(k-1));
    }
}

lemma brazilian_factorial_step(n: nat)
    requires n >= 1
    ensures brazilian_factorial(n) == factorial(n) * brazilian_factorial(n-1)
    #[trigger(brazilian_factorial(n))]
    #[trigger(brazilian_factorial(n-1))]
{
    if n == 1 {
        assert(brazilian_factorial(1) == factorial(1) * brazilian_factorial(0));
    } else {
        assert(brazilian_factorial(n) == factorial(n) * brazilian_factorial(n-1));
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
    if n == 0 {
        Some(1)
    } else {
        let mut prod = 1u64;
        let mut fact = 1u64;
        for i in 1..=n {
            match fact.checked_mul(i as u64) {
                Some(new_fact) => fact = new_fact,
                None => return None,
            }
            match prod.checked_mul(fact) {
                Some(new_prod) => prod = new_prod,
                None => return None,
            }
        }
        Some(prod)
    }
}
// </vc-code>

} // verus!
fn main() {}