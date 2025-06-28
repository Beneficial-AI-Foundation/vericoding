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
    // Simplified proof approach
    let val1 = NthDecagonalNumber(n1);
    let val2 = NthDecagonalNumber(n2);
    
    // We want to prove: 4*n2^2 - 3*n2 > 4*n1^2 - 3*n1
    // Rearranging: 4*(n2^2 - n1^2) > 3*(n2 - n1)
    // Factoring: 4*(n2 - n1)*(n2 + n1) > 3*(n2 - n1)
    
    assert(n2 >= n1 + 1);
    let diff = n2 - n1;
    assert(diff >= 1);
    
    // Since diff > 0, we can divide both sides by diff:
    // We need to show: 4*(n2 + n1) > 3
    // Since n1 >= 0 and n2 >= n1 + 1, we have n2 >= 1
    // Therefore n2 + n1 >= 1
    assert(n2 + n1 >= 1);
    assert(4 * (n2 + n1) >= 4);
    assert(4 * (n2 + n1) > 3);
    
    // Now multiply both sides by diff:
    assert(diff * 4 * (n2 + n1) > diff * 3);
    
    // This gives us:
    assert(4 * diff * (n2 + n1) > 3 * diff);
    assert(4 * (n2 - n1) * (n2 + n1) > 3 * (n2 - n1));
    assert(4 * (n2 * n2 - n1 * n1) > 3 * (n2 - n1));
    
    // Therefore:
    assert(4 * n2 * n2 - 4 * n1 * n1 > 3 * n2 - 3 * n1);
    assert(4 * n2 * n2 - 3 * n2 > 4 * n1 * n1 - 3 * n1);
    assert(val2 > val1);
}

}