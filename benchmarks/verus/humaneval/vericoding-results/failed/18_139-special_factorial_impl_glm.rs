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
/* helper modified by LLM (iteration 3): fixed overflow handling and invariant maintenance */
fn factorial_impl(n: u64) -> (ret: Option<u64>)
    ensures
        match ret {
            None => factorial(n as nat) > u64::MAX,
            Some(f) => f == factorial(n as nat),
        }
{
    if n == 0 {
        Some(1)
    } else {
        let mut fact = 1u64;
        let mut i = 1u64;
        while i <= n
            invariant
                1 <= i && i <= n+1,
                fact == factorial((i-1) as nat),
            decreases (n - i) as nat,
        {
            let new_fact = fact.checked_mul(i);
            match new_fact {
                Some(val) => fact = val,
                None => {
                    proof {
                        assert(fact * i > u64::MAX);
                    }
                    return None;
                }
            }
            i = i.checked_add(1)?;
        }
        Some(fact)
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
/* code modified by LLM (iteration 3): fixed overflow handling and invariant maintenance */
{
    let mut bf = 1u64;
    let mut i = 1u64;
    while i <= n
        invariant
            1 <= i && i <= n+1,
            bf == brazilian_factorial((i-1) as nat),
        decreases (n - i) as nat,
    {
        let fact_i = factorial_impl(i);
        match fact_i {
            None => return None,
            Some(f) => {
                let new_bf = bf.checked_mul(f);
                match new_bf {
                    Some(val) => bf = val,
                    None => {
                        proof {
                            assert(bf * f > u64::MAX);
                        }
                        return None;
                    }
                }
            }
        }
        i = i.checked_add(1)?;
    }
    Some(bf)
}
// </vc-code>

}
fn main() {}