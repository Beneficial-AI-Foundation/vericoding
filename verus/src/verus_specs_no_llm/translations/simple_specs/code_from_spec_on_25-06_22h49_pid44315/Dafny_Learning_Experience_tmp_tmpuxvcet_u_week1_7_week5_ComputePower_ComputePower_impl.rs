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
    
    // Prove that Power(n as nat) equals 2 * (n as nat) by definition
    assert(Power(n as nat) == 2 * (n as nat));
    
    // Prove that result equals Power(n as nat)
    assert(result == Power(n as nat)) by {
        // The key insight: we need to show that 2 * n as u32 equals 2 * (n as nat) as u32
        // This requires showing the arithmetic is consistent between u32 and nat
        assert(result == 2 * n);
        assert(Power(n as nat) == 2 * (n as nat));
        // For u32 values that don't overflow, u32 arithmetic matches nat arithmetic
        assert((2 * n) as nat == 2 * (n as nat));
    };
    
    result
}

}