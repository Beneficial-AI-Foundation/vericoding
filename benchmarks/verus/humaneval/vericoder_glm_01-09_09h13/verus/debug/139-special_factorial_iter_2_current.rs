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
    assert(factorial(i+1) == factorial(i) * (
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
proof fn lemma_fact_zero() {
    assert(factorial(0) == 1);
}

proof fn lemma_fact_succ(i: nat) {
    assert(factorial(i+1) == factorial(i) * (
// </vc-code>

} // verus!
fn main() {}