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
proof fn factorial_positive(n: nat)
    ensures factorial(n) >= 1
    decreases n
{
    if n <= 1 {
    } else {
        factorial_positive((n - 1) as nat);
    }
}

proof fn factorial_monotonic(n: nat)
    requires n >= 1
    ensures factorial(n + 1) > factorial(n)
{
    factorial_positive(n);
}

proof fn brazilian_factorial_positive(n: nat)
    ensures brazilian_factorial(n) >= 1
    decreases n
{
    factorial_positive(1);
    if n <= 1 {
    } else {
        factorial_positive(n);
        brazilian_factorial_positive((n - 1) as nat);
    }
}

fn factorial_impl(n: u64) -> (ret: Option<u64>)
    ensures
        match ret {
            None => factorial(n as nat) > u64::MAX,
            Some(f) => f == factorial(n as nat),
        }
{
    if n <= 1 {
        Some(1)
    } else {
        let mut result: u64 = 1;
        let mut i: u64 = 2;
        while i <= n
            invariant
                2 <= i <= n + 1,
                result == factorial((i - 1) as nat),
                result <= u64::MAX,
            decreases n - i
        {
            if result > u64::MAX / i {
                return None;
            }
            result = result * i;
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
{
    /* code modified by LLM (iteration 5): implementing recursive function with proper decreases clause */
    brazilian_factorial_impl_with_decreases(n)
}

fn brazilian_factorial_impl_with_decreases(n: u64) -> (ret: Option<u64>)
    ensures
        match ret {
            None => brazilian_factorial(n as nat) > u64::MAX,
            Some(bf) => bf == brazilian_factorial(n as nat),
        }
    decreases n
{
    if n <= 1 {
        match factorial_impl(1) {
            None => None,
            Some(f1) => Some(f1),
        }
    } else {
        match factorial_impl(n) {
            None => None,
            Some(fn_val) => {
                match brazilian_factorial_impl_with_decreases(n - 1) {
                    None => None,
                    Some(bf_prev) => {
                        if fn_val > u64::MAX / bf_prev {
                            None
                        } else {
                            Some(fn_val * bf_prev)
                        }
                    }
                }
            }
        }
    }
// </vc-code>

}
fn main() {}