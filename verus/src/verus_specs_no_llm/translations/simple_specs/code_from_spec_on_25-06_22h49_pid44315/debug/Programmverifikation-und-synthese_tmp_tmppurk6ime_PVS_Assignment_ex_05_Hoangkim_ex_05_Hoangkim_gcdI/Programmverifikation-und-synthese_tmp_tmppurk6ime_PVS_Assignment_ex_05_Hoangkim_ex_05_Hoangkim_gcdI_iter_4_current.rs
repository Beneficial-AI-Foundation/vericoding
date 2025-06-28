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

// Lemma for the GCD step property
proof fn lemma_gcd_step(a: int, b: int)
    requires a > 0 && b > 0
    ensures gcd(a, b) == gcd(b, a % b)
{
    // This follows directly from the definition of the gcd spec function
    // The definition of gcd already establishes this equality
}

// Lemma to help prove that gcd is well-defined for our use case
proof fn lemma_gcd_properties(a: int, b: int)
    requires a > 0 && b >= 0
    ensures a % b >= 0 && (b > 0 ==> a % b < b)
{
    // These are fundamental properties of modulo operation
    // Verus knows these axiomatically
}

// Helper lemma to establish the decreasing property
proof fn lemma_mod_decreases(a: int, b: int)
    requires a > 0 && b > 0
    ensures 0 <= a % b < b
{
    // This is a fundamental property of modulo
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
            lemma_gcd_step(a, b);
            lemma_gcd_properties(a, b);
            lemma_mod_decreases(a, b);
        }
        let temp = a % b;
        a = b;
        b = temp;
    }
    
    // When b == 0, gcd(a, b) == gcd(a, 0) == a by definition
    proof {
        assert(b == 0);
        assert(gcd(a, b) == a);
        assert(gcd(a, b) == gcd(m, n)); // from loop invariant
    }
    
    a
}

}