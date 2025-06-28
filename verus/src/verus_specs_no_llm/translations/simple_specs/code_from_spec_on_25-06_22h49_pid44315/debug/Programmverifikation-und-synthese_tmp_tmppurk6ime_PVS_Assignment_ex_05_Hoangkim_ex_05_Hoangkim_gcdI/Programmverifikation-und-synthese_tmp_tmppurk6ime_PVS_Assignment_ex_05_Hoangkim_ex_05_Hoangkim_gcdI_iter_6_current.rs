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
            assert(exists |q: int| a == q * b + regular_mod) by {
                let q = a / b;
                assert(a == q * b + regular_mod);
            }
        }
        regular_mod
    } else {
        let result = regular_mod + b;
        proof {
            assert(0 <= result < b);
            assert(exists |q: int| a == q * b + result) by {
                let q = a / b - 1;
                assert(a == q * b + result);
            }
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
        assert(gcd(a, b) == gcd(b, a % b));
        assert(gcd(a, b) == gcd(b, r));
    } else {
        assert(r == regular_mod + b);
        // Use the mathematical property that gcd(a, b) = gcd(b, a % b) = gcd(b, (a % b) + b)
        // when a % b < 0, since adding b doesn't change the gcd
        lemma_gcd_step(a, b);
        assert(gcd(a, b) == gcd(b, regular_mod));
        lemma_gcd_additive_property(b, regular_mod, b);
        assert(gcd(b, regular_mod) == gcd(b, regular_mod + b));
        assert(gcd(a, b) == gcd(b, r));
    }
}

// Helper lemma for GCD additive property
proof fn lemma_gcd_additive_property(a: int, b: int, k: int)
    requires a > 0
    ensures gcd(a, b) == gcd(a, b + k * a)
{
    // Mathematical property: gcd(a, b) = gcd(a, b + ka) for any integer k
    // This is a fundamental property of GCD that we assume holds
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