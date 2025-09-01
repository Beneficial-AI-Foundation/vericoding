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
proof fn brazilian_factorial_unfold(n: nat)
    ensures
        brazilian_factorial(n) == if n <= 1 {
            1
        } else {
            factorial(n) * brazilian_factorial((n - 1) as nat)
        }
    decreases n
{
    // By definition
}

proof fn factorial_positive(n: nat)
    ensures factorial(n) >= 1
    decreases n
{
    if n <= 1 {
        assert(factorial(n) == 1);
    } else {
        factorial_positive((n - 1) as nat);
        assert(factorial(n) == n * factorial((n - 1) as nat));
        assert(n >= 1);
        assert(factorial((n - 1) as nat) >= 1);
    }
}

proof fn factorial_monotonic(n: nat, m: nat)
    requires n <= m
    ensures factorial(n) <= factorial(m)
    decreases m - n
{
    if n == m {
        assert(factorial(n) == factorial(m));
    } else {
        assert(n < m);
        if m <= 1 {
            assert(n <= 1);
            assert(factorial(n) == 1);
            assert(factorial(m) == 1);
        } else {
            if n <= 1 {
                factorial_positive(m);
                assert(factorial(n) == 1);
                assert(factorial(m) >= 1);
            } else {
                factorial_monotonic((n - 1) as nat, (m - 1) as nat);
                assert(factorial(n) == n * factorial((n - 1) as nat));
                assert(factorial(m) == m * factorial((m - 1) as nat));
                assert(n <= m);
                assert(factorial((n - 1) as nat) <= factorial((m - 1) as nat));
            }
        }
    }
}

proof fn brazilian_factorial_positive(n: nat)
    ensures brazilian_factorial(n) >= 1
    decreases n
{
    if n <= 1 {
        assert(brazilian_factorial(n) == factorial(1) == 1);
    } else {
        factorial_positive(n);
        brazilian_factorial_positive((n - 1) as nat);
        assert(brazilian_factorial(n) == factorial(n) * brazilian_factorial((n - 1) as nat));
    }
}

proof fn brazilian_factorial_monotonic(n: nat, m: nat)
    requires n <= m
    ensures brazilian_factorial(n) <= brazilian_factorial(m)
    decreases m - n
{
    if n == m {
        assert(brazilian_factorial(n) == brazilian_factorial(m));
    } else {
        assert(n < m);
        if m <= 1 {
            assert(n <= 1);
            assert(brazilian_factorial(n) == 1);
            assert(brazilian_factorial(m) == 1);
        } else {
            if n <= 1 {
                brazilian_factorial_positive(m);
                assert(brazilian_factorial(n) == 1);
                assert(brazilian_factorial(m) >= 1);
            } else {
                brazilian_factorial_monotonic(n, (m - 1) as nat);
                factorial_positive(m);
                assert(brazilian_factorial(m) == factorial(m) * brazilian_factorial((m - 1) as nat));
                assert(brazilian_factorial(n) <= brazilian_factorial((m - 1) as nat));
                assert(factorial(m) >= 1);
            }
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
    // Helper function to compute factorial with overflow checking
    let factorial_with_overflow = |n: u64| -> Option<u64> {
        let mut result: u64 = 1;
        let mut i: u64 = 2;
        
        while i <= n
            invariant
                2 <= i <= n + 1,
                result == factorial((i - 1) as nat),
            decreases n - i + 1,
        {
            if let Some(new_result) = result.checked_mul(i) {
                result = new_result;
            } else {
                proof {
                    assert(result * i > u64::MAX);
                    assert(factorial(i as nat) == (i as nat) * factorial((i - 1) as nat));
                    assert(factorial(i as nat) > u64::MAX);
                    factorial_monotonic(i as nat, n as nat);
                }
                return None;
            }
            i = i + 1;
        }
        
        assert(i == n + 1);
        assert(result == factorial(n as nat));
        Some(result)
    };
    
    // Compute Brazilian factorial
    if n == 0 {
        proof {
            assert(brazilian_factorial(0) == factorial(1) == 1);
        }
        return Some(1);
    }
    
    let mut result: u64 = 1;
    let mut i: u64 = 1;
    
    while i <= n
        invariant
            1 <= i <= n + 1,
            result == brazilian_factorial((i - 1) as nat),
        decreases n - i + 1,
    {
        match factorial_with_overflow(i) {
            None => {
                proof {
                    assert(factorial(i as nat) > u64::MAX);
                    factorial_positive(i as nat);
                    brazilian_factorial_positive((i - 1) as nat);
                    assert(brazilian_factorial(i as nat) == factorial(i as nat) * brazilian_factorial((i - 1) as nat));
                    assert(brazilian_factorial(i as nat) > u64::MAX);
                    brazilian_factorial_monotonic(i as nat, n as nat);
                }
                return None;
            }
            Some(fact_i) => {
                assert(fact_i == factorial(i as nat));
                
                if let Some(new_result) = result.checked_mul(fact_i) {
                    result = new_result;
                    proof {
                        assert(result == brazilian_factorial((i - 1) as nat) * factorial(i as nat));
                        if i == 1 {
                            assert(brazilian_factorial(0) == 1);
                            assert(factorial(1) == 1);
                            assert(brazilian_factorial(1) == factorial(1) == 1);
                        } else {
                            assert(brazilian_factorial(i as nat) == factorial(i as nat) * brazilian_factorial((i - 1) as nat));
                        }
                        assert(result == brazilian_factorial(i as nat));
                    }
                } else {
                    proof {
                        assert(result * fact_i > u64::MAX);
                        assert(brazilian_factorial(i as nat) == factorial(i as nat) * brazilian_factorial((i - 1) as nat));
                        assert(brazilian_factorial(i as nat) > u64::MAX);
                        brazilian_factorial_monotonic(i as nat, n as nat);
                    }
                    return None;
                }
            }
        }
        i = i + 1;
    }
    
    assert(i == n + 1);
    assert(result == brazilian_factorial(n as nat));
    Some(result)
}
// </vc-code>

} // verus!
fn main() {}