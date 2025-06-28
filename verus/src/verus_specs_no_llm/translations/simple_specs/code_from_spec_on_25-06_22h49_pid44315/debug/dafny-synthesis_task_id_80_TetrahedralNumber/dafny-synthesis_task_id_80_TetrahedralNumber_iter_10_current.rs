use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper lemma to prove divisibility by 2 for consecutive integers
proof fn lemma_divisible_by_2(n: int)
    requires n >= 0
    ensures (n * (n + 1) * (n + 2)) % 2 == 0
{
    if n % 2 == 0 {
        // n is even, so n * (n + 1) * (n + 2) is even
        assert(n * (n + 1) * (n + 2) % 2 == 0) by(nonlinear_arith)
            requires n % 2 == 0;
    } else {
        // n is odd, so n + 1 is even, making the product even
        assert(n % 2 == 1);
        assert((n + 1) % 2 == 0) by(nonlinear_arith)
            requires n % 2 == 1;
        assert((n * (n + 1) * (n + 2)) % 2 == 0) by(nonlinear_arith)
            requires (n + 1) % 2 == 0;
    }
}

// Helper lemma to prove divisibility by 3
proof fn lemma_divisible_by_3(n: int)
    requires n >= 0
    ensures (n * (n + 1) * (n + 2)) % 3 == 0
{
    if n % 3 == 0 {
        // n is divisible by 3
        assert((n * (n + 1) * (n + 2)) % 3 == 0) by(nonlinear_arith)
            requires n % 3 == 0;
    } else if n % 3 == 1 {
        // n ≡ 1 (mod 3), so n + 2 ≡ 0 (mod 3)
        assert((n + 2) % 3 == 0) by(nonlinear_arith)
            requires n % 3 == 1;
        assert((n * (n + 1) * (n + 2)) % 3 == 0) by(nonlinear_arith)
            requires (n + 2) % 3 == 0;
    } else {
        // n ≡ 2 (mod 3), so n + 1 ≡ 0 (mod 3)
        assert(n % 3 == 2);
        assert((n + 1) % 3 == 0) by(nonlinear_arith)
            requires n % 3 == 2;
        assert((n * (n + 1) * (n + 2)) % 3 == 0) by(nonlinear_arith)
            requires (n + 1) % 3 == 0;
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
    
    // We know that product is divisible by both 2 and 3
    assert(product % 2 == 0);
    assert(product % 3 == 0);
    
    // Since product is divisible by both 2 and 3, and gcd(2,3) = 1,
    // product is divisible by 6
    assert(product % 6 == 0) by(nonlinear_arith)
        requires 
            product % 2 == 0,
            product % 3 == 0;
}

// Helper lemma to establish the exact division property
proof fn lemma_exact_division(n: int)
    requires n >= 0
    ensures 
        (n * (n + 1) * (n + 2)) % 6 == 0,
        n * (n + 1) * (n + 2) == 6 * ((n * (n + 1) * (n + 2)) / 6)
{
    lemma_tetrahedral_divisible_by_6(n);
    let product = n * (n + 1) * (n + 2);
    assert(product % 6 == 0);
    assert(product == 6 * (product / 6)) by(nonlinear_arith)
        requires product % 6 == 0;
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
        lemma_exact_division(n);
        // The division is exact, so we can safely compute it
        let product = n * (n + 1) * (n + 2);
        assert(product % 6 == 0);
        assert(product / 6 == tetrahedral_spec(n));
    }
    
    let product = n * (n + 1) * (n + 2);
    product / 6
}

}