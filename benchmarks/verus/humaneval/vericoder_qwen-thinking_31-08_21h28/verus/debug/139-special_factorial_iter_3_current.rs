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
// </vc-code>

} // verus!
fn main() {}