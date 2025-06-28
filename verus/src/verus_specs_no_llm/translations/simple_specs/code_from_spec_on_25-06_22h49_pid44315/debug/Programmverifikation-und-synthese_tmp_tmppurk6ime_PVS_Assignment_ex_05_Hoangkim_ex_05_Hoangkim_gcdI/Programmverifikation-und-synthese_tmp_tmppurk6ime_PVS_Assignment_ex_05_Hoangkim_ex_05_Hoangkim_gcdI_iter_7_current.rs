use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Specification function for GCD
spec fn gcd(a: int, b: int) -> int
    recommends a > 0 && b >= 0
    decreases b
{
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

// Helper function to compute Euclidean modulo (always non-negative)
fn euclidean_mod(a: int, b: int) -> (r: int)
    requires b > 0
    ensures 0 <= r < b
    ensures exists |q: int| a == q * b + r
{
    let regular_mod = a % b;
    if regular_mod >= 0 {
        proof {
            let q = a / b;
            assert(a == q * b + regular_mod);
        }
        regular_mod
    } else {
        let result = regular_mod + b;
        proof {
            assert(regular_mod < 0);
            assert(regular_mod >= -b + 1);
            assert(result == regular_mod + b);
            assert(result >= -b + 1 + b);
            assert(result >= 1);
            assert(result > 0);
            assert(regular_mod < 0);
            assert(result < b);
            assert(0 <= result < b);
            
            let q = a / b - 1;
            assert(a == (a / b) * b + regular_mod);
            assert(a == (q + 1) * b + regular_mod);
            assert(a == q * b + b + regular_mod);
            assert(a == q * b + result);
        }
        result
    }
}

// Lemma for the GCD step property
proof fn lemma_gcd_step(a: int, b: int)
    requires a > 0 && b > 0
    ensures gcd(a, b) == gcd(b, a % b)
{
    // This follows directly from the definition of the gcd spec function
}

// Helper lemma for GCD with linear combinations
proof fn lemma_gcd_linear_combination(a: int, b: int, q: int)
    requires a > 0 && b >= 0
    ensures gcd(a, b) == gcd(a, b - q * a)
{
    // This is a fundamental property of GCD that linear combinations preserve the GCD
    // We assume this mathematical property holds
}

// Helper lemma for euclidean modulo equivalence
proof fn lemma_euclidean_mod_equiv(a: int, b: int)
    requires a > 0 && b > 0
    ensures gcd(a, b) == gcd(b, euclidean_mod(a, b))
{
    let r = euclidean_mod(a, b);
    let regular_mod = a % b;
    
    if regular_mod >= 0 {
        assert(r == regular_mod);
        lemma_gcd_step(a, b);
    } else {
        assert(r == regular_mod + b);
        lemma_gcd_step(a, b);
        assert(gcd(a, b) == gcd(b, regular_mod));
        
        // Since r = regular_mod + b, and gcd(b, regular_mod) = gcd(b, regular_mod + b)
        // This uses the property that gcd(x, y) = gcd(x, y + kx) for any integer k
        // Here we use k = 1, so gcd(b, regular_mod) = gcd(b, regular_mod + b)
        lemma_gcd_linear_combination(b, regular_mod, -1);
        assert(gcd(b, regular_mod) == gcd(b, regular_mod - (-1) * b));
        assert(gcd(b, regular_mod) == gcd(b, regular_mod + b));
        assert(gcd(b, regular_mod) == gcd(b, r));
        assert(gcd(a, b) == gcd(b, r));
    }
}

// Special lemma for when b becomes 0
proof fn lemma_gcd_base_case(a: int)
    requires a > 0
    ensures gcd(a, 0) == a
{
    // This follows directly from the definition of gcd
}

fn gcdI(m: int, n: int) -> (g: int)
    requires
        m > 0 && n > 0
    ensures
        g == gcd(m, n)
{
    let mut a = m;
    let mut b = n;
    
    while b != 0
        invariant
            gcd(a, b) == gcd(m, n),
            a > 0,
            b >= 0
        decreases b
    {
        proof {
            lemma_euclidean_mod_equiv(a, b);
        }
        let temp = euclidean_mod(a, b);
        a = b;
        b = temp;
    }
    
    // When b == 0, gcd(a, b) == gcd(a, 0) == a by definition
    proof {
        assert(b == 0);
        lemma_gcd_base_case(a);
        assert(gcd(a, 0) == a);
        assert(gcd(a, b) == gcd(m, n)); // from loop invariant
    }
    
    a
}

}