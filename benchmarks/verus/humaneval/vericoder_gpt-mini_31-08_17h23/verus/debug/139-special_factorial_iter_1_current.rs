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
proof fn u128_mul_cast(a: u64, b: u64)
    requires (a as u128) * (b as u128) <= (u64::MAX as u128)
    ensures (( (a as u128) * (b as u128) ) as u64) as nat == (a as nat) * (b as nat)
{
    // Cast u128 product to nat equals product of nats when it fits in u64
    assert(((a as u128) * (b as u128)) as nat == (a as nat) * (b as nat));
    assert((( (a as u128) * (b as u128) ) as u64) as nat == (a as nat) * (b as nat));
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
    let mut i: u64 = 1;
    let mut fact_u64: u64 = 1; // factorial of (i-1)
    let mut bf_u64: u64 = 1; // brazilian_factorial of (i-1)

    // Loop: maintain that fact_u64 == factorial((i-1) as nat) and
    // bf_u64 == brazilian_factorial((i-1) as nat), and i in 1..=n+1
    while i <= n
        invariant i >= 1
        invariant i <= n + 1
        invariant fact_u64 as nat == factorial((i - 1) as nat)
        invariant bf_u64 as nat == brazilian_factorial((i - 1) as nat)
        decreases (n - (i - 1))
    {
        // compute next factorial: fact_u64 * i
        let prod1: u128 = (fact_u64 as u128) * (i as u128);
        if prod1 > (u64::MAX as u128) {
            return None;
        } else {
            // prod1 <= u64::MAX
            proof {
                assert((fact_u64 as u128) * (i as u128) <= (u64::MAX as u128));
                u128_mul_cast(fact_u64, i);
            }
            let new_fact: u64 = prod1 as u64;
            proof {
                // From lemma and factorial definition:
                // new_fact as nat == (fact_u64 as nat) * (i as nat) == factorial(i as nat)
                assert(new_fact as nat == (fact_u64 as nat) * (i as nat));
                assert(new_fact as nat == factorial(i as nat));
            }

            // compute next brazilian factorial: bf_u64 * new_fact
            let prod2: u128 = (bf_u64 as u128) * (new_fact as u128);
            if prod2 > (u64::MAX as u128) {
                return None;
            } else {
                proof {
                    assert((bf_u64 as u128) * (new_fact as u128) <= (u64::MAX as u128));
                    u128_mul_cast(bf_u64, new_fact);
                }
                let new_bf: u64 = prod2 as u64;
                proof {
                    // new_bf as nat == (bf_u64 as nat) * (new_fact as nat)
                    assert(new_bf as nat == (bf_u64 as nat) * (new_fact as nat));
                    // by invariant bf_u64 == brazilian_factorial(i-1) and new_fact == factorial(i)
                    assert(new_bf as nat == brazilian_factorial((i - 1) as nat) * factorial(i as nat));
                    // by definition of brazilian_factorial, brazilian_factorial(i) = factorial(i) * brazilian_factorial(i-1)
                    assert(new_bf as nat == brazilian_factorial(i as nat));
                }
                bf_u64 = new_bf;
                fact_u64 = new_fact;
                i = i + 1;
            }
        }
    }

    // After loop, i == n+1 and invariants give bf_u64 == brazilian_factorial(n)
    Some(bf_u64)
    // impl-end
}
// </vc-code>

} // verus!
fn main() {}