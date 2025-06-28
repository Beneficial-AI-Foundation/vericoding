use builtin::*;
use builtin_macros::*;

verus! {

// Spec function to define what Power means
spec fn Power(n: int) -> nat
    decreases n
{
    if n <= 0 {
        1nat
    } else {
        2 * Power(n - 1)
    }
}

// Helper lemma to prove properties about Power
proof fn lemma_power_step(i: int)
    requires i >= 0
    ensures Power(i + 1) == 2 * Power(i)
{
    // The assertion follows directly from the definition of Power
    // when i >= 0, we have i + 1 > 0, so Power(i + 1) = 2 * Power((i + 1) - 1) = 2 * Power(i)
}

// Additional helper lemma for the base case
proof fn lemma_power_zero()
    ensures Power(0) == 1
{
    // Follows directly from definition: Power(0) = 1 since 0 <= 0
}

// Helper lemma to establish Power properties for induction
proof fn lemma_power_properties(n: int)
    requires n >= 0
    ensures Power(n) >= 1
    decreases n
{
    if n == 0 {
        lemma_power_zero();
    } else {
        lemma_power_properties(n - 1);
        lemma_power_step(n - 1);
    }
}

fn main() {
}

fn ComputePower1(N: int) -> (y: nat)
    requires
        N >= 0,
        N <= 60  // Reasonable bound to prevent overflow
    ensures
        y == Power(N)
{
    if N == 0 {
        proof {
            lemma_power_zero();
        }
        return 1nat;
    }
    
    let mut result: nat = 1nat;
    let mut i: int = 0;
    
    proof {
        lemma_power_zero();
    }
    
    while i < N
        invariant
            0 <= i <= N,
            result == Power(i),
            result >= 1
        decreases N - i
    {
        proof {
            lemma_power_step(i);
            lemma_power_properties(i);
        }
        
        result = result * 2nat;
        i = i + 1;
    }
    
    result
}

}