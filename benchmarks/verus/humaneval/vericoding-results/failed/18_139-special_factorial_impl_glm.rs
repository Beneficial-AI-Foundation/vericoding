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
/* helper modified by LLM (iteration 5): changed to while loop to fix overflow and invariant issues */
fn factorial_impl(n: u64) -> (ret: Option<u64>)
    ensures
        match ret {
            None => factorial(n as nat) > u64::MAX,
            Some(f) => f == factorial(n as nat),
        }
{
    if n == 0 || n == 1 {
        Some(1)
    } else {
        let mut result = 1u64;
        let mut i = 2;
        while i <= n
            invariant
                result == factorial((i-1) as nat),
            decreases n - i,
        {
            result = result.checked_mul(i)?;
            i = i + 1;
        }
        Some(result)
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
/* code modified by LLM (iteration 5): changed to while loop to fix overflow and invariant issues */
{
    let mut bf = 1u64;
    let mut i = 1;
    while i <= n
        invariant
            bf == brazilian_factorial((i-1) as nat),
        decreases n - i,
    {
        let fact_i = factorial_impl(i)?;
        bf = bf.checked_mul(fact_i)?;
        i = i + 1;
    }
    Some(bf)
}
// </vc-code>

}
fn main() {}