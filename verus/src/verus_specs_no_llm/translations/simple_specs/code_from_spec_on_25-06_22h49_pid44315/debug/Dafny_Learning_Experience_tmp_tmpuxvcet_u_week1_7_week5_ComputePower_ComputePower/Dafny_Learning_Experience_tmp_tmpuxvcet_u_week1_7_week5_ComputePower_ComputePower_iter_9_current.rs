use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function to define what Power means
spec fn Power(n: nat) -> nat {
    2 * n
}

fn CalcPower(n: u32) -> (p: u32)
    ensures p == 2 * n
{
    2 * n
}

fn ComputePower(n: u32) -> (p: u32)
    ensures 
        p == 2 * n,
        p == Power(n as nat)
{
    let result = 2 * n;
    
    // Prove that result equals 2 * n (trivial since result is defined as 2 * n)
    assert(result == 2 * n);
    
    // Prove that Power(n as nat) equals 2 * n by definition
    assert(Power(n as nat) == 2 * (n as nat)) by {
        // This follows directly from the definition of Power
    };
    
    // Prove that result equals Power(n as nat)
    assert(result == Power(n as nat)) by {
        assert(result == 2 * n);
        assert(Power(n as nat) == 2 * (n as nat));
        assert(2 * n == 2 * (n as nat)); // u32 arithmetic matches nat arithmetic
    };
    
    result
}

}