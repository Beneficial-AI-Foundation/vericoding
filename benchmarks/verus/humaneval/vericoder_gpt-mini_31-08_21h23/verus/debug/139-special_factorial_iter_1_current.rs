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
// <vc-helpers>
lemma bf_nonzero(n: nat)
    ensures
        brazilian_factorial(n) >= 1,
{
    if n <= 1 {
        // brazilian_factorial(n) == factorial(1) == 1
    } else {
        // brazilian_factorial(n) = factorial(n) * brazilian_factorial(n-1) >= 1 * 1
        bf_nonzero(n - 1);
    }
}

lemma bf_ge_factorial(n: nat)
    requires n >= 1,
    ensures brazilian_factorial(n) >= factorial(n),
{
    if n <= 1 {
        // brazilian_factorial(1) == factorial(1)
    } else {
        // brazilian_factorial(n) = factorial(n) * brazilian_factorial(n-1) >= factorial(n) * 1
        bf_nonzero(n - 1);
    }
}

lemma bf_monotone(m: nat, n: nat)
    requires m <= n,
    ensures brazilian_factorial(m) <= brazilian_factorial(n),
{
    if m == n {
        // trivial
    } else {
        // m <= n implies m <= n-1
        bf_monotone(m, n - 1);
        // brazilian_factorial(n) = factorial(n) * brazilian_factorial(n-1) >= brazilian_factorial(n-1)
        // so brazilian_factorial(m) <= brazilian_factorial(n-1) <= brazilian_factorial(n)
    }
}

lemma nat_u128_gt(a: nat, b: nat)
    ensures (a as u128) > (b as u128) ==> a > b
{
    if a <= b {
        // then (a as u128) <= (b as u128), contradiction
    } else {
        // a > b holds
    }
}
// </vc-helpers>
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
    // impl-start
    // Compute iteratively product of factorials, detecting overflow beyond u64::MAX.
    let mut idx: u64 = 1;
    let mut fact_u128: u128 = 1u128; // equals factorial(idx-1) as u128
    let mut prod_u128: u128 = 1u128; // equals brazilian_factorial(idx-1) as u128

    while idx <= n
        invariant
            fact_u128 == factorial((idx - 1) as nat) as u128,
            prod_u128 == brazilian_factorial((idx - 1) as nat) as u128,
        decreases (n as nat) - (idx as nat) + 1
    {
        let new_fact_u128: u128 = fact_u128 * (idx as u128);
        // show new_fact_u128 equals factorial(idx) as u128
        proof {
            // factorial(idx as nat) == idx * factorial(idx-1) (holds per spec definition)
            // and fact_u128 == factorial(idx-1) as u128 by invariant
            assert(factorial((idx - 1) as nat) as u128 == fact_u128);
            // hence new_fact_u128 == factorial(idx as nat) as u128
        }

        if new_fact_u128 > (u64::MAX as u128) {
            // factorial(idx) > u64::MAX, so brazilian_factorial(n) > u64::MAX
            proof {
                let k: nat = idx as nat;
                // new_fact_u128 == factorial(k) as u128
                assert((factorial(k) as u128) == new_fact_u128);
                // so factorial(k) as u128 > u64::MAX as u128
                assert((factorial(k) as u128) > (u64::MAX as u128));
                // therefore factorial(k) > u64::MAX (as nat)
                nat_u128_gt(factorial(k), u64::MAX as nat);
                // brazilian_factorial(k) >= factorial(k)
                if k >= 1 {
                    bf_ge_factorial(k);
                }
                // brazilian_factorial(n) >= brazilian_factorial(k)
                bf_monotone(k, n as nat);
                // combine to conclude brazilian_factorial(n) > u64::MAX
            }
            return Option::None;
        }

        let new_prod_u128: u128 = prod_u128 * new_fact_u128;
        if new_prod_u128 > (u64::MAX as u128) {
            // brazilian_factorial(idx) = new_prod_u128 as nat > u64::MAX, hence brazilian_factorial(n) > u64::MAX
            proof {
                let k: nat = idx as nat;
                // new_prod_u128 == brazilian_factorial(k) as u128
                // because prod_u128 == brazilian_factorial(k-1) and new_fact_u128 == factorial(k)
                assert(prod_u128 == brazilian_factorial((idx - 1) as nat) as u128);
                assert(new_fact_u128 == factorial(k) as u128);
                // therefore new_prod_u128 == brazilian_factorial(k) as u128
                assert((brazilian_factorial(k) as u128) == new_prod_u128);
                // so brazilian_factorial(k) as u128 > u64::MAX as u128
                assert((brazilian_factorial(k) as u128) > (u64::MAX as u128));
                // hence brazilian_factorial(k) > u64::MAX
                nat_u128_gt(brazilian_factorial(k), u64::MAX as nat);
                // and brazilian_factorial(n) >= brazilian_factorial(k)
                bf_monotone(k, n as nat);
            }
            return Option::None;
        }

        // safe to update
        fact_u128 = new_fact_u128;
        prod_u128 = new_prod_u128;
        idx = idx + 1;
    }

    // finished: idx == n + 1, prod_u128 == brazilian_factorial(n) as u128
    // prod_u128 fits in u64
    proof {
        let k: nat = n as
// </vc-code>

} // verus!
fn main() {}