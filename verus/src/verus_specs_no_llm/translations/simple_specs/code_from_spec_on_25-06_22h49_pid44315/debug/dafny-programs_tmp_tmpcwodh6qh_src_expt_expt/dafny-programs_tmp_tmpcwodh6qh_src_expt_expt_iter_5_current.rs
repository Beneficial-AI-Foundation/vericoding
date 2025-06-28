use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Spec function for exponentiation
spec fn Expt(b: int, n: nat) -> int
    decreases n
{
    if n == 0 {
        1
    } else {
        b * Expt(b, n - 1)
    }
}

fn expt(b: int, n: nat) -> (res: int)
    ensures
        res == Expt(b, n)
{
    let mut result = 1;
    let mut i: nat = 0;
    
    while i < n
        invariant
            i <= n,
            result == Expt(b, i),
    {
        proof {
            // Help Verus see that Expt(b, i + 1) == b * Expt(b, i)
            assert(Expt(b, i + 1) == b * Expt(b, i)) by {
                // This follows from the definition of Expt when i + 1 > 0
                assert(i + 1 > 0);
            };
        }
        
        result = result * b;
        i = i + 1;
        
        proof {
            // After the updates: result == b * old(result) and i == old(i) + 1
            // We need to show: result == Expt(b, i)
            // This is: b * old(result) == Expt(b, old(i) + 1)
            // Which is: b * Expt(b, old(i)) == Expt(b, old(i) + 1)
            // This follows from our assertion above
        }
    }
    
    proof {
        // After the loop: i == n (since i < n is false and i <= n)
        // and result == Expt(b, i), so result == Expt(b, n)
        assert(i == n);
        assert(result == Expt(b, i));
        assert(result == Expt(b, n));
    }
    
    result
}

}