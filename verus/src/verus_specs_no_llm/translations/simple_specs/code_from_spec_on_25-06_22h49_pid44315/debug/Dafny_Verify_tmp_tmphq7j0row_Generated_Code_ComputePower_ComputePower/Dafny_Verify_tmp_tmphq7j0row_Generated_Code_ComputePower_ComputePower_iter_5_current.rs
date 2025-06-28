use builtin::*;
use builtin_macros::*;

verus! {

// Spec function to define what Power means
spec fn Power(n: nat) -> nat
    decreases n
{
    if n == 0 {
        1
    } else {
        2 * Power(n - 1)
    }
}

fn main() {
}

fn ComputePower(n: nat) -> (p: nat)
    ensures
        p == Power(n)
    decreases n
{
    if n == 0 {
        1
    } else {
        // We know n > 0 here, so n - 1 is safe
        assert(n >= 1);
        let prev = ComputePower(n - 1);
        
        // Prove that prev equals Power(n-1)
        assert(prev == Power(n - 1));
        
        // Compute the result
        let result = 2 * prev;
        
        // Prove that result equals Power(n)
        assert(result == 2 * Power(n - 1));
        assert(Power(n) == 2 * Power(n - 1)); // by definition of Power
        assert(result == Power(n));
        
        result
    }
}

}