use vstd::prelude::*;

verus! {
    // Uninterpreted function for gcd - we assume its properties through axioms
    #[verifier(uninterp)]
    spec fn gcd(a: nat, b: nat) -> nat;

    // Lemma r1: gcd(a, 0) == a
    proof fn r1(a: nat)
        ensures gcd(a, 0) == a
    {
        /* code modified by LLM (iteration 1): replaced axiom() with assume() since axiom() is not available in Verus */
        assume(gcd(a, 0) == a);
    }

    // Lemma r2: gcd(a, a) == a
    proof fn r2(a: nat)
        ensures gcd(a, a) == a
    {
        /* code modified by LLM (iteration 1): replaced axiom() with assume() since axiom() is not available in Verus */
        assume(gcd(a, a) == a);
    }

    // Lemma r3: gcd(a, b) == gcd(b, a) (commutativity)
    proof fn r3(a: nat, b: nat)
        ensures gcd(a, b) == gcd(b, a)
    {
        /* code modified by LLM (iteration 1): replaced axiom() with assume() since axiom() is not available in Verus */
        assume(gcd(a, b) == gcd(b, a));
    }

    // Lemma r4: b > 0 ==> gcd(a, b) == gcd(b, a % b) (Euclidean property)
    proof fn r4(a: nat, b: nat)
        ensures b > 0 ==> gcd(a, b) == gcd(b, a % b)
    {
        /* code modified by LLM (iteration 1): replaced axiom() with assume() since axiom() is not available in Verus */
        assume(b > 0 ==> gcd(a, b) == gcd(b, a % b));
    }

    fn GCD1(a: u32, b: u32) -> (r: u32)
        requires a > 0 && b > 0,
        ensures gcd(a as nat, b as nat) == r as nat,
        decreases b
    {
        if b == 0 {
            proof {
                r1(a as nat);
            }
            a
        } else {
            proof {
                r4(a as nat, b as nat);
            }
            GCD1(b, a % b)
        }
    }

    fn GCD2(a: u32, b: u32) -> (r: u32)
        requires a > 0 && b >= 0,
        ensures gcd(a as nat, b as nat) == r as nat,
        decreases b
    {
        if b == 0 {
            proof {
                r1(a as nat);
            }
            a
        } else {
            proof {
                r4(a as nat, b as nat);
            }
            GCD2(b, a % b)
        }
    }
}

fn main() {}