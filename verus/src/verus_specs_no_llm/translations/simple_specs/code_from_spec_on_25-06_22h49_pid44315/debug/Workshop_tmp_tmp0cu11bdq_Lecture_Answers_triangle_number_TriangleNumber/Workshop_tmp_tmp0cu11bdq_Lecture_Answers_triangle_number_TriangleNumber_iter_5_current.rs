use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper lemma to prove that N * (N + 1) is always even
proof fn lemma_consecutive_product_even(N: int)
    requires N >= 0
    ensures (N * (N + 1)) % 2 == 0
{
    if N % 2 == 0 {
        // N is even, so N * (N + 1) is even
        // Since N is even, N = 2k for some integer k
        // So N * (N + 1) = 2k * (N + 1) = 2 * (k * (N + 1))
        // Therefore N * (N + 1) is divisible by 2
        assert(N * (N + 1) % 2 == 0) by(nonlinear_arith);
    } else {
        // N is odd, so N + 1 is even, so N * (N + 1) is even
        assert(N % 2 == 1);
        // If N is odd, then N + 1 is even
        // N + 1 = 2m for some integer m
        // So N * (N + 1) = N * 2m = 2 * (N * m)
        // Therefore N * (N + 1) is divisible by 2
        assert((N + 1) % 2 == 0) by(nonlinear_arith);
        assert(N * (N + 1) % 2 == 0) by(nonlinear_arith);
    }
}

fn TriangleNumber(N: int) -> (t: int)
    requires
        N >= 0
    ensures
        t == N * (N + 1) / 2
{
    proof {
        lemma_consecutive_product_even(N);
        // The lemma proves that N * (N + 1) is even, so division by 2 is exact
        assert((N * (N + 1)) % 2 == 0);
    }
    N * (N + 1) / 2
}

}