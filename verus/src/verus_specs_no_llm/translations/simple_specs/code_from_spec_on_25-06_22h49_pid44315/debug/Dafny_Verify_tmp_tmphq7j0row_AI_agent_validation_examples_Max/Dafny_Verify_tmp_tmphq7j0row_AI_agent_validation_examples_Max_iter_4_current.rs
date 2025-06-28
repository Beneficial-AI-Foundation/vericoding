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
    if i == 0 {
        // Base case: Power(1) == 2 * Power(0)
        assert(Power(1) == 2 * Power(0));
        assert(Power(0) == 1);
        assert(Power(1) == 2 * 1);
        assert(Power(1) == 2);
    } else {
        // Inductive case follows from definition
        assert(Power(i + 1) == 2 * Power(i));
    }
}

// Additional helper lemma for the base case
proof fn lemma_power_zero()
    ensures Power(0) == 1
{
    // Follows directly from definition
}

// Additional helper lemma for positive values
proof fn lemma_power_positive(n: int)
    requires n > 0
    ensures Power(n) == 2 * Power(n - 1)
{
    // Follows directly from definition
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
            // Additional assertions to help verification
            assert(Power(i + 1) == 2 * Power(i));
            assert(result == Power(i));
            assert(result * 2 == 2 * Power(i));
            assert(result * 2 == Power(i + 1));
        }
        result = result * 2;
        i = i + 1;
        proof {
            assert(result == Power(i));
        }
    }
    
    proof {
        assert(i == N);
        assert(result == Power(i));
        assert(result == Power(N));
    }
    
    result
}

}