use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function to define the mathematical GCD
spec fn gcd(a: nat, b: nat) -> nat
    decreases b
{
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

// Lemma to help prove properties about GCD
proof fn lemma_gcd_properties(a: nat, b: nat)
    requires a > 0 && b > 0
    ensures gcd(a, b) == gcd(b, a % b)
    decreases b
{
    // The proof follows from the definition of gcd
}

proof fn lemma_gcd_positive(a: nat, b: nat)
    requires a > 0
    ensures gcd(a, b) > 0
    decreases b
{
    if b == 0 {
        // gcd(a, 0) == a > 0
    } else {
        lemma_gcd_positive(b, a % b);
    }
}

proof fn lemma_gcd_mod(a: nat, b: nat)
    requires a > 0 && b > 0
    ensures gcd(a, b) == gcd(b, a % b)
    decreases b
{
}

proof fn lemma_mod_positive(a: u32, b: u32)
    requires a > 0 && b > 0
    ensures (a % b) < b
{
}

fn gcdI(m: u32, n: u32) -> (d: u32)
    requires
        m > 0 && n > 0
    ensures
        d == gcd(m as nat, n as nat)
{
    let mut a = m;
    let mut b = n;
    
    while b != 0
        invariant
            gcd(a as nat, b as nat) == gcd(m as nat, n as nat),
            a > 0,
            b >= 0
        decreases b
    {
        proof {
            if b > 0 {
                lemma_gcd_mod(a as nat, b as nat);
                lemma_mod_positive(a, b);
                assert((a % b) < b);
            }
        }
        let temp = a % b;
        a = b;
        b = temp;
    }
    
    proof {
        assert(b == 0);
        assert(gcd(a as nat, 0) == a as nat);
    }
    
    a
}

}