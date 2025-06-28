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
        assert(n * (n + 1) == n * (n + 1));
        assert((n * (n + 1)) % 2 == 0) by {
            assert(n % 2 == 0);
        }
    } else {
        assert(n % 2 == 1);
        assert((n + 1) % 2 == 0) by {
            assert(n % 2 == 1);
            assert((n + 1) % 2 == (1 + 1) % 2);
            assert((n + 1) % 2 == 0);
        }
        assert((n * (n + 1)) % 2 == 0);
    }
}

// Helper lemma to prove divisibility by 3
proof fn lemma_divisible_by_3(n: int)
    requires n >= 0
    ensures (n * (n + 1) * (n + 2)) % 3 == 0
{
    if n % 3 == 0 {
        assert((n * (n + 1) * (n + 2)) % 3 == 0);
    } else if n % 3 == 1 {
        assert((n + 2) % 3 == 0) by {
            assert(n % 3 == 1);
            assert((n + 2) % 3 == (1 + 2) % 3);
            assert((n + 2) % 3 == 0);
        }
        assert((n * (n + 1) * (n + 2)) % 3 == 0);
    } else {
        assert(n % 3 == 2);
        assert((n + 1) % 3 == 0) by {
            assert(n % 3 == 2);
            assert((n + 1) % 3 == (2 + 1) % 3);
            assert((n + 1) % 3 == 0);
        }
        assert((n * (n + 1) * (n + 2)) % 3 == 0);
    }
}

// Helper lemma to prove divisibility by 6
proof fn lemma_tetrahedral_divisible_by_6(n: int)
    requires n >= 0
    ensures (n * (n + 1) * (n + 2)) % 6 == 0
{
    // Among any three consecutive integers n, n+1, n+2:
    // - At least one pair of consecutive integers has one even number
    // - Exactly one is divisible by 3
    // Therefore their product is divisible by 6
    
    lemma_divisible_by_2(n);
    lemma_divisible_by_3(n);
    
    let product = n * (n + 1) * (n + 2);
    
    // We know that n*(n+1) is divisible by 2
    assert((n * (n + 1)) % 2 == 0);
    // We know that n*(n+1)*(n+2) is divisible by 3
    assert(product % 3 == 0);
    
    // Since product is divisible by both 2 and 3, and gcd(2,3) = 1,
    // product is divisible by 6
    assert(product % 6 == 0) by {
        // The product n*(n+1) is even, so product = (n*(n+1))*(n+2) is even
        // The product is also divisible by 3
        // Since 2 and 3 are coprime, product is divisible by 6
        assert((n * (n + 1)) % 2 == 0);
        assert(product % 3 == 0);
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