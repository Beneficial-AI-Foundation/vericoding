use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

// Helper lemma to prove that n * (7*n - 5) is always even
proof fn lemma_nonagonal_even(n: int)
    requires n >= 0
    ensures (n * (7 * n - 5)) % 2 == 0
{
    // Case analysis on n modulo 2
    if n % 2 == 0 {
        // n is even, so n * anything is even
        // Since n is divisible by 2, n * (7*n - 5) is also divisible by 2
        assert(n % 2 == 0);
        // Use the fact that if a % 2 == 0, then (a * b) % 2 == 0 for any b
        assert((n * (7 * n - 5)) % 2 == 0) by {
            // n is even, so any multiple of n is even
            assert(n * (7 * n - 5) == (n / 2) * 2 * (7 * n - 5));
        }
    } else {
        // n is odd, so n % 2 == 1
        assert(n % 2 == 1);
        
        // When n is odd: 7*n is odd (odd * odd = odd)
        // So 7*n - 5 is even (odd - odd = even, since 5 is odd)
        let seven_n = 7 * n;
        let expr = seven_n - 5;
        
        // Prove that 7*n - 5 is even when n is odd
        assert(seven_n % 2 == 1) by {
            // 7 is odd, n is odd, so 7*n is odd
            assert(7 % 2 == 1);
            assert(n % 2 == 1);
        }
        
        assert(expr % 2 == 0) by {
            // expr = 7*n - 5, where 7*n is odd and 5 is odd
            // odd - odd = even
            assert(seven_n % 2 == 1);
            assert(5 % 2 == 1);
            assert((seven_n - 5) % 2 == 0);
        }
        
        // Now n * expr = odd * even = even
        assert((n * expr) % 2 == 0) by {
            // odd * even = even
            assert(n % 2 == 1);
            assert(expr % 2 == 0);
        }
        
        assert((n * (7 * n - 5)) % 2 == 0) by {
            assert(expr == 7 * n - 5);
            assert((n * expr) % 2 == 0);
        }
    }
}

fn NthNonagonalNumber(n: int) -> (number: int)
    requires
        n >= 0
    ensures
        number == n * (7 * n - 5) / 2
{
    let seven_n = 7 * n;
    let inner = seven_n - 5;
    let product = n * inner;
    
    proof {
        lemma_nonagonal_even(n);
        assert(product % 2 == 0);
        assert(product == n * (7 * n - 5));
    }
    
    let result = product / 2;
    
    proof {
        // Establish the final equality step by step
        assert(seven_n == 7 * n);
        assert(inner == seven_n - 5);
        assert(inner == 7 * n - 5);
        assert(product == n * inner);
        assert(product == n * (7 * n - 5));
        assert(result == product / 2);
        assert(result == n * (7 * n - 5) / 2);
    }
    
    result
}

}