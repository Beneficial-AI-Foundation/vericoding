use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn NthDecagonalNumber(n: int) -> int
    requires
        n >= 0
{
    4 * n * n - 3 * n
}

// Adding a proof function to demonstrate the spec function works correctly
proof fn test_decagonal_numbers() {
    // Verify some basic properties of decagonal numbers
    assert(NthDecagonalNumber(0) == 0);
    assert(NthDecagonalNumber(1) == 1);
    assert(NthDecagonalNumber(2) == 10);
    assert(NthDecagonalNumber(3) == 27);
}

// Helper lemma to prove monotonicity property
proof fn decagonal_monotonic(n1: int, n2: int)
    requires
        n1 >= 0,
        n2 >= n1 + 1
    ensures
        NthDecagonalNumber(n2) > NthDecagonalNumber(n1)
{
    // The proof follows from the quadratic nature of the formula
    // We need to show that 4*n2^2 - 3*n2 > 4*n1^2 - 3*n1
    // This is equivalent to showing 4*(n2^2 - n1^2) - 3*(n2 - n1) > 0
    // Which simplifies to 4*(n2 - n1)*(n2 + n1) - 3*(n2 - n1) > 0
    // Factor out (n2 - n1): (n2 - n1) * (4*(n2 + n1) - 3) > 0
    
    let diff = n2 - n1;
    assert(diff >= 1);
    
    // Since n2 >= n1 + 1 and n1 >= 0, we have n2 >= 1
    // So n2 + n1 >= 1, which means 4*(n2 + n1) >= 4
    // Therefore 4*(n2 + n1) - 3 >= 1 > 0
    assert(n2 + n1 >= n1);
    assert(4 * (n2 + n1) >= 4 * n1);
    assert(4 * (n2 + n1) - 3 >= 4 * n1 - 3);
    
    // For n1 >= 0, we need to show that 4*n1 - 3 can be handled
    // When n1 = 0: 4*(n2 + 0) - 3 = 4*n2 - 3, and since n2 >= 1, this is >= 1
    // When n1 >= 1: 4*(n2 + n1) - 3 >= 4*(1 + 1) - 3 = 5 > 0
    
    if n1 == 0 {
        assert(4 * (n2 + n1) - 3 == 4 * n2 - 3);
        assert(n2 >= 1);
        assert(4 * n2 - 3 >= 4 * 1 - 3 == 1);
    } else {
        assert(n1 >= 1);
        assert(n2 + n1 >= 2);
        assert(4 * (n2 + n1) - 3 >= 4 * 2 - 3 == 5);
    }
    
    // Now we can conclude the monotonicity
    assert(4 * (n2 + n1) - 3 > 0);
    assert(diff > 0);
    
    // The algebraic manipulation shows that NthDecagonalNumber(n2) - NthDecagonalNumber(n1) > 0
    assert(NthDecagonalNumber(n2) - NthDecagonalNumber(n1) == 
           (4 * n2 * n2 - 3 * n2) - (4 * n1 * n1 - 3 * n1));
    assert(NthDecagonalNumber(n2) - NthDecagonalNumber(n1) == 
           4 * (n2 * n2 - n1 * n1) - 3 * (n2 - n1));
    assert(NthDecagonalNumber(n2) - NthDecagonalNumber(n1) == 
           4 * (n2 - n1) * (n2 + n1) - 3 * (n2 - n1));
    assert(NthDecagonalNumber(n2) - NthDecagonalNumber(n1) == 
           (n2 - n1) * (4 * (n2 + n1) - 3));
}

}

The key changes I made:


The proof works by:
- Expanding the formula for the difference: `NthDecagonalNumber(n2) - NthDecagonalNumber(n1)`
- Factoring it as `(n2 - n1) * (4 * (n2 + n1) - 3)`
- Showing that both factors are positive when n2 >= n1 + 1 and n1 >= 0
- Therefore the product is positive, proving monotonicity