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
    // This is a basic modular arithmetic property
    assert(b == a + (b - a));
    assert(b % a == ((a + (b - a)) % a));
    assert(((a + (b - a)) % a) == ((b - a) % a)) by(nonlinear_arith);
}

// Key lemma: if we're doing modulo with the smaller number,
// one subtraction step is equivalent to the full modulo operation
// when the larger number is less than twice the smaller
proof fn gcd_one_step_lemma(smaller: int, larger: int)
    requires smaller > 0 && larger > smaller && larger < 2 * smaller
    ensures gcd(smaller, larger) == gcd(smaller, larger - smaller)
{
    assert(larger % smaller == larger - smaller) by {
        assert(larger < 2 * smaller);
        assert(larger >= smaller);
        assert(larger - smaller < smaller);
        assert(larger - smaller >= 0);
        // When larger is between smaller and 2*smaller,
        // larger % smaller == larger - smaller
    };
    assert(gcd(smaller, larger) == gcd(smaller, larger % smaller));
    assert(gcd(smaller, larger % smaller) == gcd(smaller, larger - smaller));
}

// Recursive proof for the general case
proof fn gcd_multi_step_lemma(smaller: int, larger: int)
    requires smaller > 0 && larger >= 2 * smaller
    ensures gcd(smaller, larger) == gcd(smaller, larger - smaller)
    decreases larger
{
    if larger < 2 * smaller {
        gcd_one_step_lemma(smaller, larger);
    } else {
        // larger >= 2 * smaller
        assert(gcd(smaller, larger) == gcd(smaller, larger % smaller));
        
        // Show that repeated subtraction eventually gives us larger % smaller
        let next_larger = larger - smaller;
        assert(next_larger >= smaller);
        
        if next_larger < 2 * smaller {
            gcd_one_step_lemma(smaller, next_larger);
            assert(gcd(smaller, next_larger) == gcd(smaller, next_larger - smaller));
            assert(gcd(smaller, larger - smaller) == gcd(smaller, (larger - smaller) - smaller));
        } else {
            gcd_multi_step_lemma(smaller, next_larger);
        }
        
        // The key insight: gcd(smaller, larger % smaller) can be reached
        // by repeatedly subtracting smaller from larger
        mod_subtraction_lemma(smaller, larger);
    }
}

// Helper lemma to prove GCD subtraction property
proof fn gcd_subtraction_property(a: int, b: int)
    requires a > 0 && b > 0
    ensures b > a ==> gcd(a, b) == gcd(a, b - a)
    ensures a > b ==> gcd(a, b) == gcd(a - b, b)
{
    if b > a {
        if b < 2 * a {
            gcd_one_step_lemma(a, b);
        } else {
            gcd_multi_step_lemma(a, b);
        }
    } else if a > b {
        if a < 2 * b {
            gcd_one_step_lemma(b, a);
            // gcd is commutative
            assert(gcd(a, b) == gcd(b, a));
            assert(gcd(b, a) == gcd(b, a - b));
            assert(gcd(b, a - b) == gcd(a - b, b));
        } else {
            gcd_multi_step_lemma(b, a);
            assert(gcd(a, b) == gcd(b, a));
            assert(gcd(b, a) == gcd(b, a - b));
            assert(gcd(b, a - b) == gcd(a - b, b));
        }
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
        // Prove gcd(m, n) == gcd(m-n, n) for both definitions  
        gcd_subtraction_property(n as int, m as int);
        if m - n > 0 {
            gcd_equivalence(m - n, n);
        }
    }
}

}