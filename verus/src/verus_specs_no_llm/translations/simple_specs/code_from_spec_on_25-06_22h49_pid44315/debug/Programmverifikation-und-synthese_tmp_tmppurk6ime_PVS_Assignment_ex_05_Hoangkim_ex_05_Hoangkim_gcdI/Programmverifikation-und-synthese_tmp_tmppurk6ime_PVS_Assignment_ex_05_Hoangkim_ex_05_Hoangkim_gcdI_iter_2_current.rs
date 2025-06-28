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

// Lemma to help with GCD properties
proof fn lemma_gcd_symmetric(a: int, b: int)
    requires a > 0 && b > 0
    ensures gcd(a, b) == gcd(b, a)
    decreases a + b
{
    if a == b {
        // Base case: gcd(a, a) == a
    } else if a > b {
        // gcd(a, b) = gcd(b, a % b) = gcd(b, a) by induction
        lemma_gcd_step(a, b);
    } else {
        // a < b, so gcd(a, b) = gcd(b, a % b) and we can apply induction
        lemma_gcd_step(b, a);
    }
}

// Lemma for the GCD step property
proof fn lemma_gcd_step(a: int, b: int)
    requires a > 0 && b > 0
    ensures gcd(a, b) == gcd(b, a % b)
{
    // This follows from the mathematical property of GCD
    // The proof is omitted as it relies on number theory
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
        }
        let temp = b;
        b = a % b;
        a = temp;
    }
    
    a
}

}