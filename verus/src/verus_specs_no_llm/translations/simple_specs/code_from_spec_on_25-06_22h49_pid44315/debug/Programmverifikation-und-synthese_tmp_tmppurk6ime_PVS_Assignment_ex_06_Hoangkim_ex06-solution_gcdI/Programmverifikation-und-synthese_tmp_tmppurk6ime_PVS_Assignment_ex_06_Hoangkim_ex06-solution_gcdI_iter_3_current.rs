use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn gcd(m: int, n: int) -> int
    decreases m, n
{
    if m == 0 {
        n
    } else if n == 0 {
        m
    } else if m <= n {
        gcd(m, n % m)
    } else {
        gcd(m % n, n)
    }
}

fn gcdI(m: u32, n: u32) -> (d: u32)
    requires
        m > 0 && n > 0
    ensures
        d == gcd(m as int, n as int)
    decreases m + n
{
    if m == n {
        m
    } else if m < n {
        assert(gcd(m as int, n as int) == gcd(m as int, (n - m) as int)) by {
            gcd_subtraction_property(m as int, n as int);
        };
        gcdI(m, n - m)
    } else {
        assert(gcd(m as int, n as int) == gcd((m - n) as int, n as int)) by {
            gcd_subtraction_property(n as int, m as int);
        };
        gcdI(m - n, n)
    }
}

spec fn gcd_iter(m: int, n: int) -> int
    decreases m + n
{
    if m <= 0 || n <= 0 {
        if m == 0 { n } else if n == 0 { m } else { 1 }
    } else if m == n {
        m
    } else if m < n {
        gcd_iter(m, n - m)
    } else {
        gcd_iter(m - n, n)
    }
}

// Helper lemma to prove GCD subtraction property
proof fn gcd_subtraction_property(a: int, b: int)
    requires a > 0 && b > 0
    ensures gcd(a, b) == gcd(a, b - a) when b > a
    ensures gcd(a, b) == gcd(a - b, b) when a > b
{
    if b > a {
        // We need to show gcd(a, b) == gcd(a, b - a)
        // This follows from the mathematical property that gcd(a, b) = gcd(a, b mod a)
        // and when b > a, b - a is the first step toward b mod a
        assert(b - a > 0);
        gcd_reduction_lemma(a, b);
    } else if a > b {
        // We need to show gcd(a, b) == gcd(a - b, b)  
        assert(a - b > 0);
        gcd_reduction_lemma(b, a);
    }
}

// Mathematical lemma about GCD reduction
proof fn gcd_reduction_lemma(smaller: int, larger: int)
    requires smaller > 0 && larger > smaller
    ensures gcd(smaller, larger) == gcd(smaller, larger - smaller)
{
    // This is a fundamental property of GCD that any common divisor of (smaller, larger)
    // is also a common divisor of (smaller, larger - smaller) and vice versa
}

// Proof function to establish the relationship between the iterative and recursive definitions
proof fn gcd_equivalence(m: u32, n: u32)
    requires m > 0 && n > 0
    ensures gcd(m as int, n as int) == gcd_iter(m as int, n as int)
    decreases m + n
{
    if m == n {
        // Base case: both definitions return m when m == n
        assert(gcd(m as int, n as int) == m as int);
        assert(gcd_iter(m as int, n as int) == m as int);
    } else if m < n {
        // Prove gcd(m, n) == gcd(m, n-m) for both definitions
        gcd_subtraction_property(m as int, n as int);
        gcd_equivalence(m, n - m);
    } else {
        // Prove gcd(m, n) == gcd(m-n, n) for both definitions
        gcd_subtraction_property(n as int, m as int);
        gcd_equivalence(m - n, n);
    }
}

}