use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper lemma to prove the key arithmetic identity
proof fn lemma_square_identity(i: nat)
    requires i >= 1
    ensures (i - 1) * (i - 1) + (2 * i - 1) == i * i
{
    // Expand (i-1)²
    assert((i - 1) * (i - 1) == i * i - 2 * i + 1) by (nonlinear_arith);
    // So (i-1)² + (2i-1) = i² - 2i + 1 + 2i - 1 = i²
    assert((i - 1) * (i - 1) + (2 * i - 1) == i * i - 2 * i + 1 + 2 * i - 1) by (nonlinear_arith);
    assert(i * i - 2 * i + 1 + 2 * i - 1 == i * i) by (nonlinear_arith);
}

fn sumOdds(n: nat) -> (sum: nat)
    requires
        n > 0
    ensures
        sum == n * n
{
    let mut i: nat = 1;
    let mut total: nat = 0;
    
    while i <= n
        invariant
            1 <= i <= n + 1,
            total == (i - 1) * (i - 1)
    {
        let odd_number = 2 * i - 1;
        
        // Use the lemma to prove the arithmetic identity
        proof {
            lemma_square_identity(i);
        }
        
        total = total + odd_number;
        
        // Now we can assert that total equals i²
        assert(total == i * i);
        
        i = i + 1;
        
        // After incrementing i, total == (new_i - 1)²
        // Since new_i = old_i + 1, we have total == old_i * old_i
        assert(total == (i - 1) * (i - 1));
    }
    
    // When loop exits, i == n + 1, so i - 1 == n
    // Therefore total == (i - 1) * (i - 1) == n * n
    assert(i == n + 1);
    assert(i - 1 == n);
    assert(total == n * n);
    
    total
}

}