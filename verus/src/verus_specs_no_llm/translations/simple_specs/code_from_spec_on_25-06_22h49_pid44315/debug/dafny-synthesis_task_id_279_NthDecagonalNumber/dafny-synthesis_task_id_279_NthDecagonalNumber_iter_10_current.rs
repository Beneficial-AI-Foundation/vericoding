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
    // Direct algebraic approach with more explicit steps
    let val1 = 4 * n1 * n1 - 3 * n1;
    let val2 = 4 * n2 * n2 - 3 * n2;
    
    // We want to prove: val2 > val1
    // This is equivalent to: 4*n2^2 - 3*n2 > 4*n1^2 - 3*n1
    // Rearranging: 4*(n2^2 - n1^2) - 3*(n2 - n1) > 0
    // Factoring: (n2 - n1)*(4*(n2 + n1) - 3) > 0
    
    assert(n2 >= n1 + 1);
    let diff = n2 - n1;
    assert(diff >= 1);
    assert(diff > 0);
    
    // Since n1 >= 0 and n2 >= n1 + 1, we have n2 >= 1
    assert(n2 >= 1);
    assert(n2 + n1 >= 1);
    
    // Therefore: 4*(n2 + n1) >= 4
    assert(4 * (n2 + n1) >= 4);
    assert(4 * (n2 + n1) - 3 >= 1);
    assert(4 * (n2 + n1) - 3 > 0);
    
    // Since both factors are positive:
    // diff > 0 and (4*(n2 + n1) - 3) > 0
    // Therefore: diff * (4*(n2 + n1) - 3) > 0
    
    // This means: (n2 - n1) * (4*(n2 + n1) - 3) > 0
    // Which expands to: 4*(n2^2 - n1^2) - 3*(n2 - n1) > 0
    // Which is: 4*n2^2 - 4*n1^2 - 3*n2 + 3*n1 > 0
    // Which is: (4*n2^2 - 3*n2) - (4*n1^2 - 3*n1) > 0
    // Which is: val2 - val1 > 0
    // Therefore: val2 > val1
    
    assert(val1 == NthDecagonalNumber(n1));
    assert(val2 == NthDecagonalNumber(n2));
    assert(NthDecagonalNumber(n2) > NthDecagonalNumber(n1));
}

}