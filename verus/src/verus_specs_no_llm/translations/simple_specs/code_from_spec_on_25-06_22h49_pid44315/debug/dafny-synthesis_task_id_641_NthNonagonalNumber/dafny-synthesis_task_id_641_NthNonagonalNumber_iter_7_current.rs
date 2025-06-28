use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
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
    let result = product / 2;
    
    proof {
        // First establish the basic algebraic equalities
        assert(seven_n == 7 * n);
        assert(inner == seven_n - 5 == 7 * n - 5);
        assert(product == n * inner == n * (7 * n - 5));
        
        // Now we need to prove that n * (7*n - 5) is always even for n >= 0
        // This will justify the integer division by 2
        
        // Key insight: n * (7*n - 5) = 7*n^2 - 5*n = n*(7*n - 5)
        // We prove this is even by considering cases based on n's parity
        
        if n % 2 == 0 {
            // Case 1: n is even
            // If n is even, then n * anything is even
            // So n * (7*n - 5) is even
            assert(product % 2 == 0);
        } else {
            // Case 2: n is odd (n % 2 == 1)
            // If n is odd, then 7*n is odd (since 7 is odd and odd * odd = odd)
            // Therefore 7*n - 5 is even (since 5 is odd and odd - odd = even)
            // So n * (7*n - 5) = odd * even = even
            let seven_n_mod = (7 * n) % 2;
            assert(seven_n_mod == 1); // 7*n is odd when n is odd
            let inner_mod = (7 * n - 5) % 2;
            assert(inner_mod == 0); // 7*n - 5 is even when n is odd
            assert(product % 2 == 0);
        }
        
        // Since we've proven product is even in both cases, 
        // the division by 2 is exact integer division
        assert(product % 2 == 0);
        
        // The result follows from our established equalities
        assert(result == product / 2);
        assert(result == n * (7 * n - 5) / 2);
    }
    
    result
}

}