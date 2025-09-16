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
/* helper modified by LLM (iteration 5): monotonicity of brazilian_factorial */
proof fn brazilian_factorial_monotone(k: nat, n: nat)
    requires
        k <= n,
    ensures
        brazilian_factorial(k) <= brazilian_factorial(n),
    decreases
        n,
{
    if n == k {
    } else {
        brazilian_factorial_monotone(k, (n - 1) as nat);
        proof {
            assert(brazilian_factorial(n) == factorial(n) * brazilian_factorial((n - 1) as nat));
            assert(brazilian_factorial(k) <= brazilian_factorial((n - 1) as nat));
            assert(factorial(n) >= 1);
            assert(factorial(n) * brazilian_factorial(k) <= factorial(n) * brazilian_factorial((n - 1) as nat));
            assert(brazilian_factorial(k) <= factorial(n) * brazilian_factorial((n - 1) as nat));
        }
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
/* code modified by LLM (iteration 5): iterative computation with u128 to detect overflow and return None when exceeds u64::MAX */
{
    let max128: u128 = u128::from(u64::MAX);
    let mut k: u64 = 1;
    let mut fact: u128 = 1;
    let mut accum: u128 = 1;
    while k <= n
        invariant
            fact == factorial((k - 1) as nat) as u128,
            accum == brazilian_factorial((k - 1) as nat) as u128,
            (k as nat) <= (n as nat) + 1,
        decreases
            (n as nat) - (k as nat),
    {
        fact = fact * (k as u128);
        if accum > max128 / fact {
            proof {
                assert(accum * fact > max128);
                assert((brazilian_factorial(k as nat) as u128) == fact * accum);
                brazilian_factorial_monotone(k as nat, n as nat);
                assert((brazilian_factorial(n as nat) as u128) >= (brazilian_factorial(k as nat) as u128));
                assert((brazilian_factorial(n as nat) as u128) > max128);
                assert(brazilian_factorial(n as nat) > u64::MAX);
            }
            return None;
        }
        accum = accum * fact;
        k = k + 1;
    }
    proof {
        assert(!(k <= n));
        assert((k as nat) <= (n as nat) + 1);
        assert((k as nat) == (n as nat) + 1);
        assert(accum == brazilian_factorial((k - 1) as nat) as u128);
        assert(accum == brazilian_factorial(n as nat) as u128);
        assert(accum <= max128);
    }
    let res: u64 = accum as u64;
    Some(res)
}
// </vc-code>

}
fn main() {}