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
            // Prove that Expt(b, i + 1) == b * Expt(b, i)
            // This follows from the definition since i + 1 > 0
            assert(Expt(b, i + 1) == b * Expt(b, (i + 1) - 1));
            assert((i + 1) - 1 == i);
            assert(Expt(b, i + 1) == b * Expt(b, i));
        }
        
        result = result * b;
        i = i + 1;
        
        proof {
            // The invariant should now hold
            assert(result == Expt(b, i));
        }
    }
    
    proof {
        // After the loop: i >= n (loop condition) and i <= n (invariant), so i == n
        assert(i >= n);  // from loop termination condition
        assert(i <= n);  // from loop invariant
        assert(i == n);
        assert(result == Expt(b, i));
        assert(result == Expt(b, n));
    }
    
    result
}

}