use builtin::*;
use builtin_macros::*;

verus! {

// Spec function to define what Power means
spec fn Power(n: int) -> nat
    decreases n
{
    if n <= 0 {
        1
    } else {
        2 * Power(n - 1)
    }
}

// Helper lemma to prove properties about Power
proof fn lemma_power_step(i: int)
    requires i >= 0
    ensures Power(i + 1) == 2 * Power(i)
{
    // The proof is automatic for this simple case
}

// Additional helper lemma for the base case
proof fn lemma_power_zero()
    ensures Power(0) == 1
{
    // Automatic
}

// Additional helper lemma for positive values
proof fn lemma_power_positive(n: int)
    requires n > 0
    ensures Power(n) == 2 * Power(n - 1)
{
    // Automatic by definition
}

fn main() {
}

fn ComputePower1(N: int) -> (y: nat)
    requires
        N >= 0
    ensures
        y == Power(N)
{
    if N == 0 {
        proof {
            lemma_power_zero();
        }
        return 1;
    }
    
    let mut result: nat = 1;
    let mut i: int = 0;
    
    while i < N
        invariant
            0 <= i <= N,
            result == Power(i)
        decreases N - i
    {
        proof {
            lemma_power_step(i);
        }
        result = result * 2;
        i = i + 1;
    }
    
    result
}

}