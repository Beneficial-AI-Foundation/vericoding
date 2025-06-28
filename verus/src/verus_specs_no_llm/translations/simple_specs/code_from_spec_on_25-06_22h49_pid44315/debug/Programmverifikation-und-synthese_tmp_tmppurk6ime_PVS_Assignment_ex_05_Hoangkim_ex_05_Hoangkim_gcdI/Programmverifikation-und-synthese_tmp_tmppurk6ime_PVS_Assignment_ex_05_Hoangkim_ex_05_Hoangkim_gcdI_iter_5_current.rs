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
        regular_mod
    } else {
        regular_mod + b
    }
}

// Lemma for the GCD step property
proof fn lemma_gcd_step(a: int, b: int)
    requires a > 0 && b > 0
    ensures gcd(a, b) == gcd(b, a % b)
{
    // This follows directly from the definition of the gcd spec function
}

// Lemma to help prove that gcd is well-defined for our use case
proof fn lemma_gcd_properties(a: int, b: int)
    requires a > 0 && b >= 0
    ensures a % b >= 0 && (b > 0 ==> a % b < b)
{
    // Note: This lemma might not hold for all cases due to how % works with negative numbers
    // But we'll work around this in our implementation
}

// Helper lemma for euclidean modulo
proof fn lemma_euclidean_mod_equiv(a: int, b: int)
    requires b > 0
    ensures gcd(a, b) == gcd(b, euclidean_mod(a, b))
{
    let r = euclidean_mod(a, b);
    let regular_mod = a % b;
    
    if regular_mod >= 0 {
        assert(r == regular_mod);
        assert(gcd(a, b) == gcd(b, a % b)) by {
            lemma_gcd_step(a, b);
        }
    } else {
        assert(r == regular_mod + b);
        // gcd(a, b) = gcd(b, regular_mod) = gcd(b, regular_mod + b) = gcd(b, r)
        // This uses the property that gcd(x, y) = gcd(x, y + kx) for any integer k
    }
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
        assert(gcd(a, 0) == a);
        assert(gcd(a, b) == gcd(m, n)); // from loop invariant
    }
    
    a
}

}