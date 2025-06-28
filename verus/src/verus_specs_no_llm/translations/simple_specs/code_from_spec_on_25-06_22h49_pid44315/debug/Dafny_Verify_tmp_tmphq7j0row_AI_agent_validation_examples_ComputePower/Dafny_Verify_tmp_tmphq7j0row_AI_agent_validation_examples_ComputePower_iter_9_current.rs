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
            
            proof {
                // After the updates: result = old(result) * 2, i = old(i) + 1
                // From invariant before update: old(result) == Power(old(i))
                // So: result == old(result) * 2 == Power(old(i)) * 2
                // Since i == old(i) + 1, we have old(i) == i - 1
                // We need to show: result == Power(i)
                // We know: result == Power(i - 1) * 2
                // By definition of Power when i > 0: Power(i) == 2 * Power(i - 1)
                assert(i > 0); // Since i was incremented from >= 0
                assert(i - 1 >= 0); // This helps with the Power definition
            }
        }
        
        result
    }
}

}