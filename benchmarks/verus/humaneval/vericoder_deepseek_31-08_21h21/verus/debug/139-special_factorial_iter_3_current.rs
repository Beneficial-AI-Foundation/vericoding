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
proof fn factorial_bounds(n: nat)
    ensures
        factorial(n) >= 1,
    decreases n,
{
    if n > 1 {
        factorial_bounds((n - 1) as nat);
    }
}

proof fn brazilian_factorial_bounds(n: nat)
    ensures
        brazilian_factorial(n) >= 1,
    decreases n,
{
    if n > 1 {
        let prev = (n - 1) as nat;
        factorial_bounds(n);
        brazilian_factorial_bounds(prev);
    }
}

proof fn factorial_monotonic(m: nat, n: nat)
    requires m <= n,
    ensures factorial(m) <= factorial(n),
    decreases n - m,
{
    if m < n {
        factorial_monotonic(m, (n - 1) as nat);
    }
}

proof fn brazilian_factorial_recursive(n: nat)
    ensures
        n > 1 ==> brazilian_factorial(n) == factorial(n) * brazilian_factorial((n - 1) as nat),
    decreases n,
{
    if n > 1 {
        // The definition of brazilian_factorial already provides this
    }
}

spec fn brazilian_factorial_upper_bound(n: nat) -> nat
    decreases n,
{
    if n <= 1 {
        1
    } else {
        factorial(n) * brazilian_factorial_upper_bound((n - 1) as nat)
    }
}

proof fn brazilian_factorial_le_upper_bound(n: nat)
    ensures brazilian_factorial(n) <= brazilian_factorial_upper_bound(n),
    decreases n,
{
    if n > 1 {
        brazilian_factorial_le_upper_bound((n - 1) as nat);
    }
}

proof fn factorial_upper_bound(n: nat)
    ensures factorial(n) <= 2u64.pow((n as u32)) as nat,
    decreases n,
{
    if n <= 1 {
    } else {
        factorial_upper_bound((n - 1) as nat);
    }
}

proof fn brazilian_factorial_upper_bound_estimate(n: nat)
    ensures brazilian_factorial_upper_bound(n) <= 2u64.pow(((n * (n + 1) / 2) as u32)) as nat,
    decreases n,
{
    if n > 1 {
        brazilian_factorial_upper_bound_estimate((n - 1) as nat);
    }
}

spec fn compute_factorial(n: u64) -> Option<u64> {
    if n == 0 {
        Some(1)
    } else {
        let prev = compute_factorial(n - 1);
        match prev {
            Some(p) => (n as u64).checked_mul(p),
            None => None,
        }
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
    if n == 0 {
        proof {
            brazilian_factorial_bounds(0);
        }
        return Some(1);
    }
    
    let mut result: u64 = 1;
    let mut k: u64 = 1;
    
    while k <= n
        invariant
            k <= n + 1,
            result == brazilian_factorial((k - 1) as nat),
            result >= 1,
        decreases n - k,
    {
        let current_factorial = match compute_factorial(k) {
            Some(f) => f,
            None => return None,
        };
        
        proof {
            brazilian_factorial_recursive(k as nat);
        }
        
        let product = match result.checked_mul(current_factorial) {
            Some(p) => p,
            None => return None,
        };
        
        result = product;
        k = k + 1;
    }
    
    Some(result)
}
// </vc-code>

} // verus!
fn main() {}