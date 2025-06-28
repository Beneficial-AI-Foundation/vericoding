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
        // If N is even, then N = 2k for some integer k
        // So N * (N + 1) = 2k * (N + 1) = 2 * (k * (N + 1))
        // Therefore, N * (N + 1) is divisible by 2
        assert(N * (N + 1) == N * (N + 1));
        assert((N * (N + 1)) % 2 == 0) by {
            // Since N % 2 == 0, we know N is even
            // An even number times any integer is even
        };
    } else {
        // N is odd, so N + 1 is even, so N * (N + 1) is even
        // If N is odd, then N % 2 == 1, so (N + 1) % 2 == 0
        assert((N + 1) % 2 == 0) by {
            // If N % 2 == 1, then N + 1 ≡ 1 + 1 ≡ 0 (mod 2)
            assert(N % 2 == 1);
            assert((N + 1) % 2 == (N % 2 + 1 % 2) % 2);
            assert((N + 1) % 2 == (1 + 1) % 2);
            assert((N + 1) % 2 == 2 % 2);
            assert((N + 1) % 2 == 0);
        };
        assert((N * (N + 1)) % 2 == 0) by {
            // Since (N + 1) % 2 == 0, we know N + 1 is even
            // Any integer times an even number is even
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