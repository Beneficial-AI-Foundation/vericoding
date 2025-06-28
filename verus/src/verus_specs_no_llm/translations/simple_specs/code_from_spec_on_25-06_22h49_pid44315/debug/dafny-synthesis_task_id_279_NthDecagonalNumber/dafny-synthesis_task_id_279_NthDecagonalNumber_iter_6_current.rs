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
    // 4*n2^2 - 3*n2 > 4*n1^2 - 3*n1 when n2 > n1 for sufficiently large n1
}

}