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
    let mut i: u32 = 1;
    let mut total: u32 = 0;
    
    while i <= n
        invariant
            1 <= i <= n + 1,
            total == (i - 1) * (i - 1),
            i <= u32::MAX,
            total <= u32::MAX,
            n <= u32::MAX
    {
        let odd_number = 2 * i - 1;
        
        // Use the lemma to prove the arithmetic identity
        proof {
            lemma_square_identity(i as nat);
            assert(total as nat == (i as nat - 1) * (i as nat - 1));
            assert(odd_number as nat == 2 * i as nat - 1);
            assert((i as nat - 1) * (i as nat - 1) + (2 * i as nat - 1) == i as nat * i as nat);
        }
        
        // Before updating total, we have total == (i-1)²
        // The lemma tells us that (i-1)² + (2*i-1) == i²
        total = total + odd_number;
        
        // Now total == i² by the lemma
        proof {
            assert(total as nat == i as nat * i as nat);
        }
        
        i = i + 1;
        
        // After incrementing i, the new value of i is old_i + 1
        // So (i - 1) = old_i, and total == old_i² == (i - 1)²
        // This maintains the loop invariant
        proof {
            assert(total as nat == (i as nat - 1) * (i as nat - 1));
        }
    }
    
    // When loop exits, i == n + 1, so total == (n + 1 - 1)² == n²
    proof {
        assert(i as nat == n + 1);
        assert(total as nat == (i as nat - 1) * (i as nat - 1));
        assert(total as nat == n * n);
    }
    
    total as nat
}

}