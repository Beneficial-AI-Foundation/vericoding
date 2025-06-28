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
        assert((N * (N + 1)) % 2 == 0);
    } else {
        // N is odd, so N + 1 is even, so N * (N + 1) is even
        assert((N + 1) % 2 == 0);
        assert((N * (N + 1)) % 2 == 0);
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
    }
    N * (N + 1) / 2
}

}