use vstd::prelude::*;

verus! {

spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
}

// <vc-helpers>
proof fn factorial_positive(n: nat)
    ensures factorial(n) > 0
    decreases n
{
    if n == 0 {
        assert(factorial(0) == 1);
    } else {
        factorial_positive((n - 1) as nat);
        assert(factorial((n - 1) as nat) > 0);
        assert(n > 0);
        assert(factorial(n) == n * factorial((n - 1) as nat));
    }
}

proof fn factorial_values()
    ensures 
        factorial(0) == 1,
        factorial(1) == 1,
        factorial(2) == 2,
        factorial(3) == 6,
        factorial(4) == 24,
        factorial(5) == 120,
        factorial(6) == 720,
        factorial(7) == 5040,
        factorial(8) == 40320,
        factorial(9) == 362880,
        factorial(10) == 3628800,
        factorial(11) == 39916800,
        factorial(12) == 479001600,
{
    assert(factorial(0) == 1);
    assert(factorial(1) == 1 * factorial(0) == 1 * 1 == 1);
    assert(factorial(2) == 2 * factorial(1) == 2 * 1 == 2);
    assert(factorial(3) == 3 * factorial(2) == 3 * 2 == 6);
    assert(factorial(4) == 4 * factorial(3) == 4 * 6 == 24);
    assert(factorial(5) == 5 * factorial(4) == 5 * 24 == 120);
    assert(factorial(6) == 6 * factorial(5) == 6 * 120 == 720);
    assert(factorial(7) == 7 * factorial(6) == 7 * 720 == 5040);
    assert(factorial(8) == 8 * factorial(7) == 8 * 5040 == 40320);
    assert(factorial(9) == 9 * factorial(8) == 9 * 40320 == 362880);
    assert(factorial(10) == 10 * factorial(9) == 10 * 362880 == 3628800);
    assert(factorial(11) == 11 * factorial(10) == 11 * 3628800 == 39916800);
    assert(factorial(12) == 12 * factorial(11) == 12 * 39916800 == 479001600);
}

proof fn factorial_monotonic(n: nat)
    requires n >= 1
    ensures factorial(n) >= factorial((n - 1) as nat)
    decreases n
{
    factorial_positive((n - 1) as nat);
    assert(factorial(n) == n * factorial((n - 1) as nat));
    assert(n >= 1);
}

proof fn factorial_bounded(n: nat)
    requires n <= 12
    ensures factorial(n) <= i32::MAX
    decreases n
{
    factorial_values();
    assert(i32::MAX == 2147483647);
    if n == 0 {
        assert(factorial(0) == 1);
    } else if n == 1 {
        assert(factorial(1) == 1);
    } else if n == 2 {
        assert(factorial(2) == 2);
    } else if n == 3 {
        assert(factorial(3) == 6);
    } else if n == 4 {
        assert(factorial(4) == 24);
    } else if n == 5 {
        assert(factorial(5) == 120);
    } else if n == 6 {
        assert(factorial(6) == 720);
    } else if n == 7 {
        assert(factorial(7) == 5040);
    } else if n == 8 {
        assert(factorial(8) == 40320);
    } else if n == 9 {
        assert(factorial(9) == 362880);
    } else if n == 10 {
        assert(factorial(10) == 3628800);
    } else if n == 11 {
        assert(factorial(11) == 39916800);
    } else if n == 12 {
        assert(factorial(12) == 479001600);
    }
}
// </vc-helpers>

// <vc-spec>
fn compute_factorial(n: i32) -> (u: i32)
    requires 1 <= n,
    ensures u == factorial(n as nat),
// </vc-spec>
// <vc-code>
{
    let mut result: i32 = 1;
    let mut i: i32 = 2;
    
    if n <= 12 {
        proof {
            factorial_bounded(n as nat);
        }
    }
    
    proof {
        factorial_values();
        assert(factorial(0) == 1);
        assert(factorial(1) == 1);
    }
    assert(result == factorial(1 as nat));
    
    while i <= n
        invariant 
            2 <= i <= n + 1,
            result == factorial((i - 1) as nat),
            1 <= result,
            n <= 12 ==> factorial(n as nat) <= i32::MAX,
            n <= 12 ==> factorial((i - 1) as nat) <= i32::MAX,
            n <= 12 ==> result <= i32::MAX,
            n <= 12 ==> i <= 12,
        decreases n - i + 1
    {
        proof {
            factorial_positive((i - 1) as nat);
            assert(factorial(i as nat) == (i as nat) * factorial((i - 1) as nat));
            if n <= 12 {
                assert(i <= n);
                assert(i <= 12);
                factorial_bounded(i as nat);
                assert(factorial(i as nat) <= i32::MAX);
                assert(result == factorial((i - 1) as nat));
                assert(result >= 1);
                assert(i >= 2);
                assert(i <= 12);
                assert(result * i == factorial(i as nat));
                assert(factorial(i as nat) <= i32::MAX);
            }
        }
        
        assert(n <= 12 ==> result * i <= i32::MAX);
        result = result * i;
        assert(i < i32::MAX);
        i = i + 1;
    }
    
    assert(i == n + 1);
    assert(result == factorial((i - 1) as nat));
    assert(result == factorial(n as nat));
    result
}
// </vc-code>

fn main() {
}

}