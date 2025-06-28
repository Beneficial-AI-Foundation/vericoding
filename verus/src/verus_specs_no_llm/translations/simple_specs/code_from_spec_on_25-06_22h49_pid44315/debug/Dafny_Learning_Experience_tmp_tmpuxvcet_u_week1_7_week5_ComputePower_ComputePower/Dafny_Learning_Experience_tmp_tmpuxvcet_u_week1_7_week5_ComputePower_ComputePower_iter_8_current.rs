use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function to define what Power means
spec fn Power(n: nat) -> nat {
    2 * n
}

fn CalcPower(n: nat) -> (p: nat)
    ensures p == 2 * n
{
    2 * n
}

fn ComputePower(n: nat) -> (p: nat)
    ensures 
        p == 2 * n,
        p == Power(n)
{
    let result = 2 * n;
    
    // Prove that result equals 2 * n (trivial since result is defined as 2 * n)
    assert(result == 2 * n);
    
    // Prove that Power(n) equals 2 * n by definition
    assert(Power(n) == 2 * n) by {
        // This follows directly from the definition of Power
    };
    
    // Prove that result equals Power(n)
    assert(result == Power(n)) by {
        assert(result == 2 * n);
        assert(Power(n) == 2 * n);
    };
    
    result
}

}