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
    let mut prod: u64 = 1;
    let mut fact: u64 = 1;
    let mut k: u64 = 1;

    while k <= n {
        invariant(
            k >= 1 && 
            k <= n+1 && 
            (prod as nat == brazilian_factorial((k-1) as nat)) &&
            (fact as nat == factorial((k-1) as nat))
        );

        if fact > u64::MAX / k {
            return None;
        }
        fact = fact * k;

        if prod > u64::MAX / fact {
            return None;
        }
        prod = prod * fact;

        k = k + 1;
    }
    Some(prod)
}
// </vc-code>

} // verus!
fn main() {}