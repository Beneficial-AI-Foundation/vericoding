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
        let prev = ComputePower((n - 1) as nat);
        
        // The result of multiplication in nat domain
        let result = (2 * prev) as nat;
        
        // Verus can automatically prove this by unfolding the definition
        assert(Power(n) == 2 * Power((n - 1) as nat)) by {
            // Power(n) unfolds to 2 * Power(n - 1) when n > 0
        };
        
        result
    }
}

}