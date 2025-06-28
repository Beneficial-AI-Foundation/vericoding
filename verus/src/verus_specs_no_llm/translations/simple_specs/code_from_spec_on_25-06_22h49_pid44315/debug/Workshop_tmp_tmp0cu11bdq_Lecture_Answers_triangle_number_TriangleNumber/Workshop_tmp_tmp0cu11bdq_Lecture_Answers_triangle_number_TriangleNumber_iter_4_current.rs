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
        // Since N is even, N * anything is even
        assert(N * (N + 1) == N * (N + 1));
        // The product of an even number and any integer is even
    } else {
        // N is odd, so N + 1 is even, so N * (N + 1) is even
        assert(N % 2 == 1);
        // If N is odd, then N + 1 is even
        // The product of any integer and an even number is even
        assert((N + 1) % 2 == 0) by {
            // Since consecutive integers have opposite parity
            // and N is odd, N + 1 must be even
            assert(N % 2 == 1);
            // For any odd number n, n + 1 is even
        };
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