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
        assert(N * (N + 1) % 2 == 0) by(nonlinear_arith);
    } else {
        // N is odd, so N + 1 is even, so N * (N + 1) is even
        assert(N % 2 == 1);
        assert((N + 1) % 2 == 0) by(nonlinear_arith);
        assert(N * (N + 1) % 2 == 0) by(nonlinear_arith);
    }
}

// Helper lemma to establish the exact division property
proof fn lemma_triangle_division(N: int)
    requires N >= 0
    ensures 
        (N * (N + 1)) % 2 == 0,
        N * (N + 1) / 2 * 2 == N * (N + 1)
{
    lemma_consecutive_product_even(N);
    
    // Since we know N * (N + 1) is even, we can use the division property
    let product = N * (N + 1);
    assert(product % 2 == 0);
    
    // For any even integer x, x / 2 * 2 == x
    assert(product / 2 * 2 == product) by {
        assert(product % 2 == 0);
        // This follows from the definition of division for even numbers
        assert(exists|k: int| product == 2 * k) by(nonlinear_arith);
        assert(product / 2 * 2 == product) by(nonlinear_arith);
    };
    
    assert(N * (N + 1) / 2 * 2 == N * (N + 1));
}

fn TriangleNumber(N: int) -> (t: int)
    requires
        N >= 0
    ensures
        t == N * (N + 1) / 2
{
    proof {
        lemma_triangle_division(N);
    }
    N * (N + 1) / 2
}

}