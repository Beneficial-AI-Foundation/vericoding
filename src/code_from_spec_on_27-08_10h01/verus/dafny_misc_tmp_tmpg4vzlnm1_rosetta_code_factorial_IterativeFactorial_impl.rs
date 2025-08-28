use vstd::prelude::*;

verus! {

// recursive definition of factorial
spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
}

// iterative implementation of factorial

// <vc-helpers>
spec fn factorial_iter_spec(i: nat, acc: nat, n: nat) -> nat
    decreases n - i
{
    if i >= n {
        acc
    } else {
        factorial_iter_spec(i + 1, acc * (i + 1), n)
    }
}

proof fn factorial_iter_correctness(n: nat)
    ensures factorial_iter_spec(0, 1, n) == factorial(n)
    decreases n
{
    if n == 0 {
    } else {
        factorial_iter_helper(0, 1, n);
    }
}

proof fn factorial_iter_helper(i: nat, acc: nat, n: nat)
    requires i <= n, acc == factorial(i)
    ensures factorial_iter_spec(i, acc, n) == factorial(n)
    decreases n - i
{
    if i >= n {
    } else {
        assert(acc * (i + 1) == factorial(i + 1)) by {
            assert(factorial(i + 1) == (i + 1) * factorial(i));
            assert(acc == factorial(i));
        }
        factorial_iter_helper(i + 1, acc * (i + 1), n);
    }
}

proof fn factorial_bounds(n: nat)
    requires n <= 12
    ensures factorial(n) <= 6227020800
    decreases n
{
    if n == 0 {
        assert(factorial(0) == 1);
    } else if n == 1 {
        assert(factorial(1) == 1) by {
            assert(factorial(1) == 1 * factorial(0));
            assert(factorial(0) == 1);
        }
    } else if n == 2 {
        assert(factorial(2) == 2) by {
            assert(factorial(2) == 2 * factorial(1));
            assert(factorial(1) == 1);
        }
    } else if n == 3 {
        assert(factorial(3) == 6) by {
            assert(factorial(3) == 3 * factorial(2));
            assert(factorial(2) == 2);
        }
    } else if n == 4 {
        assert(factorial(4) == 24) by {
            assert(factorial(4) == 4 * factorial(3));
            assert(factorial(3) == 6);
        }
    } else if n == 5 {
        assert(factorial(5) == 120) by {
            assert(factorial(5) == 5 * factorial(4));
            assert(factorial(4) == 24);
        }
    } else if n == 6 {
        assert(factorial(6) == 720) by {
            assert(factorial(6) == 6 * factorial(5));
            assert(factorial(5) == 120);
        }
    } else if n == 7 {
        assert(factorial(7) == 5040) by {
            assert(factorial(7) == 7 * factorial(6));
            assert(factorial(6) == 720);
        }
    } else if n == 8 {
        assert(factorial(8) == 40320) by {
            assert(factorial(8) == 8 * factorial(7));
            assert(factorial(7) == 5040);
        }
    } else if n == 9 {
        assert(factorial(9) == 362880) by {
            assert(factorial(9) == 9 * factorial(8));
            assert(factorial(8) == 40320);
        }
    } else if n == 10 {
        assert(factorial(10) == 3628800) by {
            assert(factorial(10) == 10 * factorial(9));
            assert(factorial(9) == 362880);
        }
    } else if n == 11 {
        assert(factorial(11) == 39916800) by {
            assert(factorial(11) == 11 * factorial(10));
            assert(factorial(10) == 3628800);
        }
    } else if n == 12 {
        assert(factorial(12) == 479001600) by {
            assert(factorial(12) == 12 * factorial(11));
            assert(factorial(11) == 39916800);
        }
    }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn iterative_factorial(n: u32) -> (result: u32)
    requires n < 13, // prevent overflow
    ensures result == factorial(n as nat)
// </vc-spec>
// </vc-spec>

// <vc-code>
{
    proof {
        factorial_iter_correctness(n as nat);
        factorial_bounds(n as nat);
    }
    
    let mut i: u32 = 0;
    let mut acc: u32 = 1;
    
    while i < n
        invariant 
            i <= n,
            acc == factorial(i as nat),
            factorial_iter_spec(i as nat, acc as nat, n as nat) == factorial(n as nat),
            factorial(i as nat) <= 6227020800,
            factorial(n as nat) <= 6227020800
        decreases n - i
    {
        i = i + 1;
        proof {
            factorial_bounds(i as nat);
        }
        acc = acc * i;
        
        proof {
            assert(acc == factorial(i as nat)) by {
                assert(factorial(i as nat) == i * factorial((i - 1) as nat));
            }
        }
    }
    
    acc
}
// </vc-code>

fn main() {}

}