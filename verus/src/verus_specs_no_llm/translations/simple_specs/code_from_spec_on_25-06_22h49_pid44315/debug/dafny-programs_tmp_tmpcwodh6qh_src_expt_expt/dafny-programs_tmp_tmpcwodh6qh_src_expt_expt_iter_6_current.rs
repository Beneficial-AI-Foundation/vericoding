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
        // Before updating, establish the relationship we need
        assert(Expt(b, i + 1) == b * Expt(b, i)) by {
            if i + 1 == 0 {
                // This case is impossible since i >= 0, so i + 1 >= 1
                assert(false);
            } else {
                // When i + 1 > 0, Expt(b, i + 1) = b * Expt(b, (i + 1) - 1) = b * Expt(b, i)
                // This follows directly from the definition of Expt
            }
        };
        
        result = result * b;
        i = i + 1;
        
        // The invariant should now hold:
        // result == old(result) * b == Expt(b, old(i)) * b == Expt(b, old(i) + 1) == Expt(b, i)
        assert(result == Expt(b, i));
    }
    
    // After the loop: i >= n and i <= n (from invariant), so i == n
    assert(i == n);
    assert(result == Expt(b, i));
    assert(result == Expt(b, n));
    
    result
}

}