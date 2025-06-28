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

// Helper proof to show the modulo relationship
proof fn mod_subtraction_lemma(a: int, b: int)
    requires a > 0 && b > a
    ensures b % a == (b - a) % a
{
    assert(b % a == (b - a) % a) by(nonlinear_arith);
}

// Key lemma: GCD subtraction property
proof fn gcd_subtraction_property(a: int, b: int)
    requires a > 0 && b > a
    ensures gcd(a, b) == gcd(a, b - a)
{
    // The key insight is that gcd(a, b) = gcd(a, b % a)
    // and when b > a but b < 2*a, then b % a = b - a
    
    if b < 2 * a {
        // When b < 2*a, we have b % a = b - a
        assert(b % a == b - a) by(nonlinear_arith);
        assert(gcd(a, b) == gcd(a, b % a));
        assert(gcd(a, b % a) == gcd(a, b - a));
    } else {
        // When b >= 2*a, we need to show that repeated subtraction
        // eventually gives us the same result as modulo
        let remainder = b % a;
        assert(remainder >= 0 && remainder < a) by(nonlinear_arith);
        assert(gcd(a, b) == gcd(a, remainder));
        
        // Now we need to connect this to the subtraction step
        // The key insight is that gcd(a, b) = gcd(a, b-a) because
        // any common divisor of a and b is also a common divisor of a and b-a
        assert(gcd(a, b) == gcd(a, b - a)) by {
            // This follows from the fundamental property that
            // gcd(x, y) = gcd(x, y - x) for any x, y
            assert(forall |x: int, y: int| x > 0 && y > x ==> gcd(x, y) == gcd(x, y - x)) by(nonlinear_arith);
        };
    }
}

// Proof function to establish the relationship between the iterative and recursive definitions
proof fn gcd_equivalence(m: u32, n: u32)
    requires m > 0 && n > 0
    ensures gcd(m as int, n as int) == gcd_iter(m as int, n as int)
    decreases m + n
{
    if m == n {
        // Base case: both definitions return m when m == n
        assert(gcd_iter(m as int, n as int) == m as int);
    } else if m < n {
        // Prove gcd(m, n) == gcd(m, n-m) for both definitions
        gcd_subtraction_property(m as int, n as int);
        if n - m > 0 {
            gcd_equivalence(m, n - m);
        }
    } else {
        // m > n case
        gcd_subtraction_property(n as int, m as int);
        if m - n > 0 {
            gcd_equivalence(m - n, n);
        }
    }
}

}