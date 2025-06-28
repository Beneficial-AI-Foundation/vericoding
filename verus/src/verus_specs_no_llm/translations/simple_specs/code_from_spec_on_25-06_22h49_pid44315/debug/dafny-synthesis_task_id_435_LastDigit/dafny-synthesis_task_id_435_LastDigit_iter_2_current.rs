use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn LastDigit(n: int) -> (d: int)
    requires
        n >= 0
    ensures
        0 <= d < 10,
        n % 10 == d
{
    let result = n % 10;
    
    // Proof that the result is in the correct range
    assert(result >= 0) by {
        // For non-negative n, n % 10 >= 0
    };
    
    assert(result < 10) by {
        // For any n, n % 10 < 10
    };
    
    result
}

}

The key changes I made:




The function preserves all the original specifications:
- **Requires clause**: `n >= 0` (unchanged)
- **Ensures clauses**: `0 <= d < 10` and `n % 10 == d` (unchanged)
- **Function signature**: Same parameter and return types
- **Implementation logic**: Still returns `n % 10`

This should now verify successfully as Verus can prove that for any non-negative integer `n`, the expression `n % 10` will always be between 0 and 9 inclusive.