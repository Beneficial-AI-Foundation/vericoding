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
proof fn fact_nonzero(n: nat)
    ensures factorial(n) >= 1,
    decreases n,
{
    if n <= 1 {
        // factorial(0) == 1, factorial(1) == 1
        assert(factorial(n) == 1);
    } else {
        fact_nonzero(n - 1);
        proof {
            // factorial(n) = n * factorial(n-1) and n >= 2 implies >= 1
            assert(factorial(n) == n * factorial(n - 1));
            assert(n >= 1);
            assert(factorial(n - 1) >= 1);
            // product of two nats >= 1
        }
    }
}

proof fn bf_nonzero(n: nat)
    ensures
        brazilian_factorial(n) >= 1,
    decreases n,
{
    if n <= 1 {
        // brazilian_factorial(0) == factorial(1) == 1
        assert(brazilian_factorial(n) == factorial(1));
        assert(factorial(1) == 1);
    } else {
        bf_nonzero(n - 1);
        fact_nonzero(n);
        proof {
            // brazilian_factorial(n) = factorial(n) * brazilian_factorial(n-1)
            assert(brazilian_factorial(n) == factorial(n) * brazilian_factorial(n - 1));
            assert(factorial(n) >= 1);
            assert(brazilian_factorial(n - 1) >= 1);
            // product >= 1
        }
    }
}

proof fn bf_ge_factorial(n: nat)
    requires n >= 1,
    ensures brazilian_factorial(n) >= factorial(n),
    decreases n,
{
    if n <= 1 {
        // n == 1: brazilian_factorial(1) == factorial(1)
        assert(n == 1);
        assert(brazilian_factorial(n) == factorial(n));
    } else {
        // n > 1
        bf_nonzero(n - 1);
        proof {
            // brazilian_factorial(n) = factorial(n) * brazilian_factorial(n-1) >= factorial(n) * 1 == factorial(n)
            assert(brazilian_factorial(n) == factorial(n) * brazilian_factorial(n - 1));
            assert(brazilian_factorial(n - 1) >= 1);
            // hence >= factorial(n)
        }
    }
}

proof fn bf_monotone(m: nat, n: nat)
    requires m <= n,
    ensures brazilian_factorial(m) <= brazilian_factorial(n),
    decreases n,
{
    if m == n {
        // trivial
        assert(brazilian_factorial(m) == brazilian_factorial(n));
    } else {
        // m <= n-1
        bf_monotone(m, n - 1);
        fact_nonzero(n);
        proof {
            // brazilian_factorial(n) = factorial(n) * brazilian_factorial(n-1) >= brazilian_factorial(n-1)
            assert(brazilian_factorial(n) == factorial(n) * brazilian_factorial(n - 1));
            assert(factorial(n) >= 1);
            // so bf(m) <= bf(n-1) <= bf(n)
        }
    }
}

proof fn nat_u128_gt(a: nat, b: nat)
    ensures (a as u128) > (b as u128) ==> a > b,
    decreases a, b,
{
    if a <= b {
        // then (a as u128) <= (b as u128), so antecedent is false; implication holds
        assert((a as u128) <= (b as u128));
    } else {
        // a > b, so implication holds
        assert(a > b);
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
    // impl-start
    // Compute iteratively product of factorials, detecting overflow beyond u64::MAX.
    let mut idx: u64 = 1;
    let mut fact_u128: u128 = 1u128; // equals factorial(idx-1) as u128
    let mut prod_u128: u128 = 1u128; // equals brazilian_factorial(idx-1) as u128

    while idx <= n
        invariant
            fact_u128 == factorial((idx - 1) as nat) as u128,
            prod_u128 == brazilian_factorial((idx - 1) as nat) as u128,
            prod_u128 <= (u64::MAX as u128),
            idx <= n + 1,
        decreases (n as nat) - (idx as nat) + 1
    {
        let new_fact_u128: u128 = fact_u128 * (idx as u128);
        // show new_fact_u128 equals factorial(idx) as u128
        proof {
            let k: nat = idx as nat;
            // idx starts at 1, so k >= 1 and k - 1 is valid
            assert(fact_u128 == factorial(k - 1) as u128);
            if k <= 1 {
                // k == 1
                assert(factorial(k) == 1);
                assert(new_fact_u128 == 1u128);
                assert(new_fact_u128 == factorial(k) as u128);
            } else {
                // k > 1: factorial(k) = k * factorial(k-1)
                assert(factorial(k) == k * factorial(k - 1));
                assert(new_fact_u128 == (factorial(k - 1) as u128) * (k as u128));
                assert(new_fact_u128 == factorial(k) as u128);
            }
        }

        if new_fact_u128 > (u64::MAX as u128) {
            // factorial(idx) > u64::MAX, so brazilian_factorial(n) > u64::MAX
            proof {
                let k: nat = idx as nat;
                assert(new_fact_u128 == factorial(k) as u128);
                assert(new_fact_u128 > (u64::MAX as u128));
                nat_u128_gt(factorial(k), u64::MAX as nat);
                // factorial(k) > u64::MAX in nat
                // brazilian_factorial(k) = factorial(k) * brazilian_factorial(k-1) >= factorial(k) * 1
                bf_nonzero(k - 1);
                assert(brazilian_factorial(k) == factorial(k) * brazilian_factorial(k - 1));
                assert(brazilian_factorial(k) >= factorial(k));
                // so brazilian_factorial(k) > u64::MAX
                nat_u128_gt(brazilian_factorial(k), u64::MAX as nat);
                // and brazilian_factorial(n) >= brazilian_factorial(k)
                bf_monotone(k, n as nat);
            }
            return Option::None;
        }

        let new_prod_u128: u128 = prod_u128 * new_fact_u128;
        if new_prod_u128 > (u64::MAX as u128) {
            // brazilian_factorial(idx) = new_prod_u128 as nat > u64::MAX, hence brazilian_factorial(n) > u64::MAX
            proof {
                let k: nat = idx as nat;
                assert(prod_u128 == brazilian_factorial((idx - 1) as nat) as u128);
                assert(new_fact_u128 == factorial(k) as u128);
                assert((brazilian_factorial(k) as u128) == new_prod_u128);
                assert((brazilian_factorial(k) as u128) > (u64::MAX as u128));
                nat_u128_gt(brazilian_factorial(k), u64::MAX as nat);
                bf_monotone(k, n as nat);
            }
            return Option::None;
        }

        // safe to update
        fact_u128 = new_fact_u128;
        prod_u128 = new_prod_u128;
        idx = idx + 1;
    }

    // finished: idx == n + 1, prod_u128 == brazilian_factorial(n) as u128 and prod_u128 <= u64::MAX
    proof {
        let k: nat = n as nat;
        assert(idx > n);
        assert(idx <= n + 1);
        assert(idx == n + 1);
        assert(prod_u128 == brazilian_factorial((idx - 1) as nat) as u128);
        assert((idx - 1) as nat == k);
        assert(prod_u128 == brazilian_factorial(k) as u128);
        assert(prod_u128 <= (u64::MAX as u128));
    }

    let res: u64 = prod_u128 as u64;
    // show res equals brazilian_factorial(n as nat)
    proof {
        let k: nat = n as nat;
        assert(prod_u128 == brazilian_factorial(k) as u128);
        assert((res as u128) == prod_u128);
        assert(res == brazilian_factorial(k) as u64);
    }
    return Option::Some(res);
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}