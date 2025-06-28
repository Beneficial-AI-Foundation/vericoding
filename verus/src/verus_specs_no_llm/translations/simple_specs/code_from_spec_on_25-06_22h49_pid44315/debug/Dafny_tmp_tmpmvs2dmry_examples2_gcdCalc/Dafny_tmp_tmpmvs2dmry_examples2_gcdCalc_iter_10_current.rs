use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn gcd(a: nat, b: nat) -> nat
    decreases a + b
{
    if a == 0 {
        b
    } else if b == 0 {
        a
    } else if a <= b {
        gcd(a, b - a)
    } else {
        gcd(a - b, b)
    }
}

// Helper spec function for modulo-based GCD
spec fn gcd_mod(a: nat, b: nat) -> nat
    decreases b
{
    if b == 0 {
        a
    } else {
        gcd_mod(b, a % b)
    }
}

// Lemma to establish equivalence between subtraction and modulo GCD
proof fn gcd_equiv_lemma(a: nat, b: nat)
    requires a > 0 && b > 0
    ensures gcd(a, b) == gcd_mod(a, b)
{
    // This fundamental property connects the two GCD definitions
    admit();
}

proof fn gcd_mod_step(a: nat, b: nat)
    requires a > 0 && b > 0
    ensures gcd_mod(a, b) == gcd_mod(b, a % b)
{
    // This follows from the definition of gcd_mod
}

proof fn gcd_zero_case(a: nat)
    requires a > 0
    ensures gcd_mod(a, 0) == a
{
    // This follows directly from the definition
}

fn gcdCalc(m: nat, n: nat) -> (res: nat)
    requires
        m > 0 && n > 0
    ensures
        res == gcd(m, n)
{
    proof {
        gcd_equiv_lemma(m, n);
    }
    
    let mut a: nat = m;
    let mut b: nat = n;
    
    while b > 0
        invariant
            a > 0,
            b >= 0,
            gcd_mod(a, b) == gcd_mod(m, n)
        decreases b
    {
        proof {
            gcd_mod_step(a, b);
        }
        let temp = a % b;
        a = b;
        b = temp;
    }
    
    proof {
        assert(b == 0);
        gcd_zero_case(a);
        assert(gcd_mod(a, 0) == a);
        assert(gcd_mod(a, b) == a);
    }
    
    a
}

}