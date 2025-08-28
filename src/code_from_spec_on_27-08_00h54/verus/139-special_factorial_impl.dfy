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
proof fn lemma_factorial_positive(n: nat)
    ensures
        factorial(n) >= 1,
    decreases n,
{
    if (n == 0) {
    } else {
        lemma_factorial_positive((n - 1) as nat);
        assert(factorial(n) >= 1) by {
            broadcast use lemma_mul_strictly_positive;
        };
    }
}

proof fn lemma_brazilian_factorial_positive(n: nat)
    ensures
        brazilian_factorial(n) >= 1,
    decreases n,
{
    if (n == 0) {
    } else {
        lemma_factorial_positive((n) as nat);
        lemma_brazilian_factorial_positive((n - 1) as nat);
        assert(brazilian_factorial(n) >= 1) by {
            lemma_mul_strictly_positive(
                factorial(n) as int,
                brazilian_factorial((n - 1) as nat) as int,
            )
        };
    }
}

proof fn lemma_brazilian_fib_monotonic(i: nat, j: nat)
    requires
        0 <= i <= j,
    ensures
        brazilian_factorial(i) <= brazilian_factorial(j),
    decreases j - i,
{
    if (i == j) {
    } else if (j == i + 1) {
        assert(factorial(j) >= 1) by { lemma_factorial_positive(j) };
        assert(brazilian_factorial(j) >= brazilian_factorial(i)) by {
            broadcast use lemma_mul_increases;
        };
    } else {
        lemma_brazilian_fib_monotonic(i, (j - 1) as nat);
        lemma_brazilian_fib_monotonic((j - 1) as nat, j);
    }
}

fn factorial_impl(n: u64) -> (ret: Option<u64>)
    ensures
        match ret {
            None => factorial(n as nat) > u64::MAX,
            Some(f) => f == factorial(n as nat),
        },
    decreases n,
{
    if n <= 1 {
        Some(1)
    } else {
        match factorial_impl(n - 1) {
            None => {
                proof {
                    assert(factorial((n - 1) as nat) > u64::MAX);
                    assert(factorial(n as nat) == n * factorial((n - 1) as nat));
                    assert(factorial(n as nat) > u64::MAX);
                }
                None
            }
            Some(f_prev) => {
                if f_prev > u64::MAX / n {
                    proof {
                        assert(f_prev == factorial((n - 1) as nat));
                        assert(factorial(n as nat) == n * factorial((n - 1) as nat));
                        assert(factorial(n as nat) == n * f_prev);
                        assert(f_prev > u64::MAX / n);
                        assert(n * f_prev > u64::MAX);
                        assert(factorial(n as nat) > u64::MAX);
                    }
                    None
                } else {
                    proof {
                        assert(f_prev == factorial((n - 1) as nat));
                        assert(factorial(n as nat) == n * factorial((n - 1) as nat));
                        assert(factorial(n as nat) == n * f_prev);
                        assert(f_prev <= u64::MAX / n);
                        assert(n * f_prev <= u64::MAX);
                    }
                    Some(n * f_prev)
                }
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
decreases n,
{
    if n <= 1 {
        Some(1)
    } else {
        match factorial_impl(n) {
            None => {
                proof {
                    assert(factorial(n as nat) > u64::MAX);
                    assert(brazilian_factorial(n as nat) == factorial(n as nat) * brazilian_factorial((n - 1) as nat));
                    lemma_brazilian_factorial_positive((n - 1) as nat);
                    assert(brazilian_factorial((n - 1) as nat) >= 1);
                    assert(brazilian_factorial(n as nat) >= factorial(n as nat));
                    assert(brazilian_factorial(n as nat) > u64::MAX);
                }
                None
            }
            Some(f) => {
                match brazilian_factorial_impl(n - 1) {
                    None => {
                        proof {
                            assert(brazilian_factorial((n - 1) as nat) > u64::MAX);
                            assert(brazilian_factorial(n as nat) == factorial(n as nat) * brazilian_factorial((n - 1) as nat));
                            assert(brazilian_factorial(n as nat) > u64::MAX);
                        }
                        None
                    }
                    Some(bf_prev) => {
                        if bf_prev == 0 || f > u64::MAX / bf_prev {
                            proof {
                                assert(f == factorial(n as nat));
                                assert(bf_prev == brazilian_factorial((n - 1) as nat));
                                assert(brazilian_factorial(n as nat) == factorial(n as nat) * brazilian_factorial((n - 1) as nat));
                                assert(brazilian_factorial(n as nat) == f * bf_prev);
                                if bf_prev == 0 {
                                    lemma_brazilian_factorial_positive((n - 1) as nat);
                                    assert(false);
                                } else {
                                    assert(f > u64::MAX / bf_prev);
                                    assert(f * bf_prev > u64::MAX);
                                    assert(brazilian_factorial(n as nat) > u64::MAX);
                                }
                            }
                            None
                        } else {
                            proof {
                                assert(f == factorial(n as nat));
                                assert(bf_prev == brazilian_factorial((n - 1) as nat));
                                assert(brazilian_factorial(n as nat) == factorial(n as nat) * brazilian_factorial((n - 1) as nat));
                                assert(brazilian_factorial(n as nat) == f * bf_prev);
                                assert(f <= u64::MAX / bf_prev);
                                assert(f * bf_prev <= u64::MAX);
                            }
                            Some(f * bf_prev)
                        }
                    }
                }
            }
        }
    }
}
// </vc-code>

} // verus!
fn main() {}