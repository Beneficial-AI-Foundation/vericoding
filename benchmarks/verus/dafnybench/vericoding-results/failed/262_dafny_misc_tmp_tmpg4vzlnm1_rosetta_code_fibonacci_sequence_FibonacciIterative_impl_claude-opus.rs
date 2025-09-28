use vstd::prelude::*;

verus! {

// definition of Fibonacci numbers
spec fn fibonacci(n: nat) -> nat
    decreases n
{
    if n == 0 {
        0
    } else if n == 1 {
        1
    } else {
        fibonacci((n - 1) as nat) + fibonacci((n - 2) as nat)
    }
}

// iterative calculation of Fibonacci numbers

// <vc-helpers>
// Helper lemma to ensure fibonacci values don't overflow for small inputs
proof fn fibonacci_bound_lemma(n: nat)
    requires n < 94
    ensures fibonacci(n) < u64::MAX
    decreases n
{
    if n == 0 {
        assert(fibonacci(0) == 0);
        assert(0 < u64::MAX);
    } else if n == 1 {
        assert(fibonacci(1) == 1);
        assert(1 < u64::MAX);
    } else if n < 20 {
        // For small values, compute recursively
        fibonacci_bound_lemma((n - 1) as nat);
        fibonacci_bound_lemma((n - 2) as nat);
        // Compute and verify specific values
        if n == 2 { 
            assert(fibonacci(1) == 1);
            assert(fibonacci(0) == 0);
            assert(fibonacci(2) == fibonacci(1) + fibonacci(0) == 1 + 0 == 1); 
        }
        else if n == 3 { 
            assert(fibonacci(2) == 1) by { fibonacci_bound_lemma(2); }
            assert(fibonacci(1) == 1);
            assert(fibonacci(3) == fibonacci(2) + fibonacci(1) == 1 + 1 == 2); 
        }
        else if n == 4 { 
            assert(fibonacci(3) == 2) by { fibonacci_bound_lemma(3); }
            assert(fibonacci(2) == 1) by { fibonacci_bound_lemma(2); }
            assert(fibonacci(4) == fibonacci(3) + fibonacci(2) == 2 + 1 == 3); 
        }
        else if n == 5 { 
            assert(fibonacci(4) == 3) by { fibonacci_bound_lemma(4); }
            assert(fibonacci(3) == 2) by { fibonacci_bound_lemma(3); }
            assert(fibonacci(5) == fibonacci(4) + fibonacci(3) == 3 + 2 == 5); 
        }
        else if n == 6 { 
            assert(fibonacci(5) == 5) by { fibonacci_bound_lemma(5); }
            assert(fibonacci(4) == 3) by { fibonacci_bound_lemma(4); }
            assert(fibonacci(6) == fibonacci(5) + fibonacci(4) == 5 + 3 == 8); 
        }
        else if n == 7 { 
            assert(fibonacci(6) == 8) by { fibonacci_bound_lemma(6); }
            assert(fibonacci(5) == 5) by { fibonacci_bound_lemma(5); }
            assert(fibonacci(7) == fibonacci(6) + fibonacci(5) == 8 + 5 == 13); 
        }
        else if n == 8 { 
            assert(fibonacci(7) == 13) by { fibonacci_bound_lemma(7); }
            assert(fibonacci(6) == 8) by { fibonacci_bound_lemma(6); }
            assert(fibonacci(8) == fibonacci(7) + fibonacci(6) == 13 + 8 == 21); 
        }
        else if n == 9 { 
            assert(fibonacci(8) == 21) by { fibonacci_bound_lemma(8); }
            assert(fibonacci(7) == 13) by { fibonacci_bound_lemma(7); }
            assert(fibonacci(9) == fibonacci(8) + fibonacci(7) == 21 + 13 == 34); 
        }
        else if n == 10 { 
            assert(fibonacci(9) == 34) by { fibonacci_bound_lemma(9); }
            assert(fibonacci(8) == 21) by { fibonacci_bound_lemma(8); }
            assert(fibonacci(10) == fibonacci(9) + fibonacci(8) == 34 + 21 == 55); 
        }
        else if n == 11 { 
            assert(fibonacci(10) == 55) by { fibonacci_bound_lemma(10); }
            assert(fibonacci(9) == 34) by { fibonacci_bound_lemma(9); }
            assert(fibonacci(11) == fibonacci(10) + fibonacci(9) == 55 + 34 == 89); 
        }
        else if n == 12 { 
            assert(fibonacci(11) == 89) by { fibonacci_bound_lemma(11); }
            assert(fibonacci(10) == 55) by { fibonacci_bound_lemma(10); }
            assert(fibonacci(12) == fibonacci(11) + fibonacci(10) == 89 + 55 == 144); 
        }
        else if n == 13 { 
            assert(fibonacci(12) == 144) by { fibonacci_bound_lemma(12); }
            assert(fibonacci(11) == 89) by { fibonacci_bound_lemma(11); }
            assert(fibonacci(13) == fibonacci(12) + fibonacci(11) == 144 + 89 == 233); 
        }
        else if n == 14 { 
            assert(fibonacci(13) == 233) by { fibonacci_bound_lemma(13); }
            assert(fibonacci(12) == 144) by { fibonacci_bound_lemma(12); }
            assert(fibonacci(14) == fibonacci(13) + fibonacci(12) == 233 + 144 == 377); 
        }
        else if n == 15 { 
            assert(fibonacci(14) == 377) by { fibonacci_bound_lemma(14); }
            assert(fibonacci(13) == 233) by { fibonacci_bound_lemma(13); }
            assert(fibonacci(15) == fibonacci(14) + fibonacci(13) == 377 + 233 == 610); 
        }
        else if n == 16 { 
            assert(fibonacci(15) == 610) by { fibonacci_bound_lemma(15); }
            assert(fibonacci(14) == 377) by { fibonacci_bound_lemma(14); }
            assert(fibonacci(16) == fibonacci(15) + fibonacci(14) == 610 + 377 == 987); 
        }
        else if n == 17 { 
            assert(fibonacci(16) == 987) by { fibonacci_bound_lemma(16); }
            assert(fibonacci(15) == 610) by { fibonacci_bound_lemma(15); }
            assert(fibonacci(17) == fibonacci(16) + fibonacci(15) == 987 + 610 == 1597); 
        }
        else if n == 18 { 
            assert(fibonacci(17) == 1597) by { fibonacci_bound_lemma(17); }
            assert(fibonacci(16) == 987) by { fibonacci_bound_lemma(16); }
            assert(fibonacci(18) == fibonacci(17) + fibonacci(16) == 1597 + 987 == 2584); 
        }
        else if n == 19 { 
            assert(fibonacci(18) == 2584) by { fibonacci_bound_lemma(18); }
            assert(fibonacci(17) == 1597) by { fibonacci_bound_lemma(17); }
            assert(fibonacci(19) == fibonacci(18) + fibonacci(17) == 2584 + 1597 == 4181); 
        }
    } else {
        // For larger values, we use the exponential growth property
        // fibonacci(n) < 2^n for all n
        fibonacci_exponential_bound(n);
    }
}

proof fn fibonacci_exponential_bound(n: nat)
    ensures fibonacci(n) < pow2(n)
    decreases n
{
    if n == 0 {
        assert(fibonacci(0) == 0);
        assert(pow2(0) == 1);
    } else if n == 1 {
        assert(fibonacci(1) == 1);
        assert(pow2(1) == 2 * pow2(0) == 2 * 1 == 2);
    } else {
        fibonacci_exponential_bound((n - 1) as nat);
        fibonacci_exponential_bound((n - 2) as nat);
        assert(fibonacci(n) == fibonacci((n - 1) as nat) + fibonacci((n - 2) as nat));
        assert(fibonacci((n - 1) as nat) < pow2((n - 1) as nat));
        assert(fibonacci((n - 2) as nat) < pow2((n - 2) as nat));
        assert(pow2((n - 2) as nat) + pow2((n - 2) as nat) == 2 * pow2((n - 2) as nat));
        assert(2 * pow2((n - 2) as nat) == pow2((n - 1) as nat)) by {
            pow2_doubles((n - 2) as nat);
        }
        assert(pow2((n - 1) as nat) + pow2((n - 2) as nat) < pow2((n - 1) as nat) + pow2((n - 1) as nat));
        assert(pow2((n - 1) as nat) + pow2((n - 1) as nat) == 2 * pow2((n - 1) as nat));
        assert(2 * pow2((n - 1) as nat) == pow2(n)) by {
            pow2_doubles((n - 1) as nat);
        }
    }
}

spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        2 * pow2((n - 1) as nat)
    }
}

proof fn pow2_doubles(n: nat)
    ensures pow2(n + 1) == 2 * pow2(n)
{
    assert(pow2(n + 1) == 2 * pow2(((n + 1) - 1) as nat));
    assert(((n + 1) - 1) as nat == n);
}
// </vc-helpers>

// <vc-spec>
fn fibonacci_iterative(n: u64) -> (f: u64)
    requires n < 100  // practical bound to prevent overflow
    ensures f == fibonacci(n as nat)
// </vc-spec>
// <vc-code>
{
    if n == 0 {
        return 0;
    } else if n == 1 {
        return 1;
    }
    
    // Check precondition for loop invariant
    assert(n < 100);
    assert(n < 94) by {
        assert(n < 100);
        assert(94 <= 100);
    }
    
    let mut a: u64 = 0;  // fibonacci(0)
    let mut b: u64 = 1;  // fibonacci(1)
    let mut i: u64 = 1;
    
    while i < n
        invariant
            1 <= i <= n,
            a == fibonacci((i - 1) as nat),
            b == fibonacci(i as nat),
            i < 94,
            n < 94,
        decreases n - i
    {
        proof {
            fibonacci_bound_lemma(i as nat);
            fibonacci_bound_lemma((i + 1) as nat);
        }
        let next = a + b;
        a = b;
        b = next;
        i = i + 1;
        
        assert(a == fibonacci((i - 1) as nat));
        assert(b == fibonacci(i as nat));
    }
    
    assert(i == n);
    assert(b == fibonacci(n as nat));
    b
}
// </vc-code>

fn main() {
}

}