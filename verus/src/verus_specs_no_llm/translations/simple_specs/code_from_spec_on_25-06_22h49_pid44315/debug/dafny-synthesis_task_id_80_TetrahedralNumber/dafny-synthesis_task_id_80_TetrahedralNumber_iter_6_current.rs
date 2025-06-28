use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper lemma to prove divisibility by 2
proof fn lemma_divisible_by_2(n: int)
    requires n >= 0
    ensures (n * (n + 1)) % 2 == 0
{
    if n % 2 == 0 {
        // n is even, so n * (n + 1) is even
        assert(n * (n + 1) % 2 == 0) by(nonlinear_arith);
    } else {
        // n is odd, so n + 1 is even
        assert(n % 2 == 1);
        assert((n + 1) % 2 == 0) by(nonlinear_arith);
        assert(n * (n + 1) % 2 == 0) by(nonlinear_arith);
    }
}

// Helper lemma to prove divisibility by 3
proof fn lemma_divisible_by_3(n: int)
    requires n >= 0
    ensures (n * (n + 1) * (n + 2)) % 3 == 0
{
    if n % 3 == 0 {
        // n is divisible by 3
        assert((n * (n + 1) * (n + 2)) % 3 == 0) by(nonlinear_arith);
    } else if n % 3 == 1 {
        // n ≡ 1 (mod 3), so n + 2 ≡ 0 (mod 3)
        assert((n + 2) % 3 == 0) by(nonlinear_arith);
        assert((n * (n + 1) * (n + 2)) % 3 == 0) by(nonlinear_arith);
    } else {
        // n ≡ 2 (mod 3), so n + 1 ≡ 0 (mod 3)
        assert(n % 3 == 2);
        assert((n + 1) % 3 == 0) by(nonlinear_arith);
        assert((n * (n + 1) * (n + 2)) % 3 == 0) by(nonlinear_arith);
    }
}

// Helper lemma to prove divisibility by 6
proof fn lemma_tetrahedral_divisible_by_6(n: int)
    requires n >= 0
    ensures (n * (n + 1) * (n + 2)) % 6 == 0
{
    lemma_divisible_by_2(n);
    lemma_divisible_by_3(n);
    
    let product = n * (n + 1) * (n + 2);
    
    // We know that n*(n+1) is divisible by 2
    assert((n * (n + 1)) % 2 == 0);
    // We know that n*(n+1)*(n+2) is divisible by 3
    assert(product % 3 == 0);
    
    // Since product is divisible by both 2 and 3, and gcd(2,3) = 1,
    // product is divisible by 6
    assert(product % 6 == 0) by(nonlinear_arith);
}

// Spec function for the tetrahedral number formula
spec fn tetrahedral_spec(n: int) -> int {
    n * (n + 1) * (n + 2) / 6
}

fn TetrahedralNumber(n: int) -> (t: int)
    requires
        n >= 0
    ensures
        t == tetrahedral_spec(n)
{
    proof {
        lemma_tetrahedral_divisible_by_6(n);
        // Additional proof that the division is exact
        let product = n * (n + 1) * (n + 2);
        assert(product % 6 == 0);
        assert(product == 6 * (product / 6)) by(nonlinear_arith);
    }
    
    let product = n * (n + 1) * (n + 2);
    product / 6
}

}