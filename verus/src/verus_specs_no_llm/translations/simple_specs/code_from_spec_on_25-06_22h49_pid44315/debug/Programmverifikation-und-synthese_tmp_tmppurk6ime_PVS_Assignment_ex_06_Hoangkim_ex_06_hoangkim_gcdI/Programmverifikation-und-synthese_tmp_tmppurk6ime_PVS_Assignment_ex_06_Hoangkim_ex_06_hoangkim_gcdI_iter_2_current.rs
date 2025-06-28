use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function to define the mathematical GCD
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

// Lemma to help prove properties about GCD
proof fn lemma_gcd_properties(a: int, b: int)
    requires a > 0 && b > 0
    ensures gcd(a, b) == gcd(b, a % b)
    decreases b
{
    // The proof follows from the definition of gcd
}

proof fn lemma_gcd_positive(a: int, b: int)
    requires a > 0 && b >= 0
    ensures gcd(a, b) > 0
    decreases b
{
    if b == 0 {
        // gcd(a, 0) == a > 0
    } else {
        lemma_gcd_positive(b, a % b);
    }
}

fn gcdI(m: int, n: int) -> (d: int)
    requires
        m > 0 && n > 0
    ensures
        d == gcd(m, n)
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
            lemma_gcd_properties(a, b);
        }
        let temp = a % b;
        a = b;
        b = temp;
    }
    
    a
}

}