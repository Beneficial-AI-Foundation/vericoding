use builtin::*;
use builtin_macros::*;

verus! {

spec fn Power(n: int) -> nat
    decreases n
{
    if n <= 0 {
        1nat
    } else {
        2nat * Power(n - 1)
    }
}

fn main() {
}

fn ComputePower(N: int) -> (y: nat)
    requires
        N >= 0
    ensures
        y == Power(N)
{
    if N == 0 {
        return 1nat;
    }
    
    let mut result: nat = 1nat;
    let mut i: int = 0;
    
    while i < N
        invariant
            0 <= i <= N,
            result == Power(i)
        decreases N - i
    {
        proof {
            // We need to prove that after the updates, result * 2 == Power(i + 1)
            // This follows from the definition of Power and the current invariant
            assert(i + 1 > 0);
            assert(Power(i + 1) == 2nat * Power(i)) by {
                assert(i + 1 > 0);
                // Since i + 1 > 0, Power(i + 1) = 2 * Power((i + 1) - 1) = 2 * Power(i)
            };
        }
        result = result * 2nat;
        i = i + 1;
    }
    
    return result;
}

}

The key fixes made:




The verification should now pass because:
- The `Power` spec function is well-defined for all integers
- The loop invariant correctly maintains that `result == Power(i)`
- The proof establishes the relationship between consecutive powers
- The function correctly computes 2^N iteratively