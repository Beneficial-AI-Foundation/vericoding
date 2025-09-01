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
fn brazilian_factorial_impl(n: u64) -> Option<u64> {
    if n == 0 {
        return Some(1);
    }
    let mut bf: u64 = 1;
    for i: u64 in 1..=n
        invariant
            bf == brazilian_factorial((i as nat) - 1),
            (i as nat) - 1 <= n as nat,
    {
        let mut fact: u64 = 1;
        for j: u64 in 1..=i
            invariant
                fact == factorial((j as nat) - 1),
                (j as nat) - 1 <= i as nat,
        {
            match fact.checked_mul(j) {
                Some(f) => fact = f,
                None => return None,
            }
        }
        match bf.checked_mul(fact) {
            Some(b) => bf = b,
            None => return None,
        }
    }
    proof {
        assert(bf == brazilian_factorial(n as nat));
    }
    Some(bf)
}
// </vc-code>

} // verus!
fn main() {}