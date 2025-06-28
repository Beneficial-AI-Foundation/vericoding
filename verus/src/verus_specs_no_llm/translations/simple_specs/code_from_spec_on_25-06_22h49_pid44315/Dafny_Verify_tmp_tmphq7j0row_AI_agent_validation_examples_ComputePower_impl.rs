use builtin::*;
use builtin_macros::*;

verus! {

// Specification function to define what Power means
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
        1nat
    } else {
        let mut result: nat = 1nat;
        let mut i: int = 0;
        
        while i < N
            invariant
                0 <= i <= N,
                result == Power(i)
            decreases N - i
        {
            result = result * 2nat;
            i = i + 1;
            
            // Help the verifier understand that after the updates,
            // the invariant still holds
            assert(i > 0); // i was incremented, so it's positive
            assert(i - 1 >= 0); // This helps with Power definition
            assert(Power(i) == 2nat * Power(i - 1)); // By definition of Power for i > 0
        }
        
        result
    }
}

}