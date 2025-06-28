use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper lemma to prove divisibility by 6
proof fn lemma_tetrahedral_divisible_by_6(n: int)
    requires n >= 0
    ensures (n * (n + 1) * (n + 2)) % 6 == 0
{
    // Among any three consecutive integers n, n+1, n+2:
    // - At least one is divisible by 2
    // - Exactly one is divisible by 3
    // Therefore their product is divisible by 6
    
    // We can prove this by case analysis on n % 6
    let product = n * (n + 1) * (n + 2);
    
    // Case analysis on n modulo 6
    if n % 6 == 0 {
        // n is divisible by 6, so product is divisible by 6
        assert(product % 6 == 0);
    } else if n % 6 == 1 {
        // n+1 is divisible by 2, n+2 is divisible by 3
        assert((n + 2) % 3 == 0);
        assert((n + 1) % 2 == 0);
        assert(product % 6 == 0);
    } else if n % 6 == 2 {
        // n is divisible by 2, n+2 is divisible by 2, one of them gives factor of 2
        // and one of n, n+1, n+2 is divisible by 3
        assert(n % 2 == 0);
        assert(product % 6 == 0);
    } else if n % 6 == 3 {
        // n is divisible by 3, n+1 is divisible by 2
        assert(n % 3 == 0);
        assert((n + 1) % 2 == 0);
        assert(product % 6 == 0);
    } else if n % 6 == 4 {
        // n is divisible by 2, n+2 is divisible by 2 and 3
        assert(n % 2 == 0);
        assert((n + 2) % 6 == 0);
        assert(product % 6 == 0);
    } else {
        // n % 6 == 5, so n+1 is divisible by 2 and 3
        assert((n + 1) % 6 == 0);
        assert(product % 6 == 0);
    }
}

fn TetrahedralNumber(n: int) -> (t: int)
    requires
        n >= 0
    ensures
        t == n * (n + 1) * (n + 2) / 6
{
    proof {
        lemma_tetrahedral_divisible_by_6(n);
    }
    
    let product = n * (n + 1) * (n + 2);
    product / 6
}

}