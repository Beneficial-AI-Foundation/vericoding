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
    let mut result: int = 1;
    let mut i: nat = 0;
    
    while i < n
        invariant
            i <= n,
            result == Expt(b, i),
    {
        // Proof that the invariant is maintained
        assert(i + 1 <= n);
        assert(result * b == Expt(b, i) * b);
        assert(Expt(b, i) * b == Expt(b, i + 1)) by {
            // This follows from the definition of Expt
            assert(Expt(b, i + 1) == b * Expt(b, (i + 1) - 1));
            assert((i + 1) - 1 == i);
        };
        
        result = result * b;
        i = i + 1;
    }
    
    // After the loop, i == n, so result == Expt(b, n)
    assert(i == n);
    assert(result == Expt(b, i));
    assert(result == Expt(b, n));
    
    result
}

}