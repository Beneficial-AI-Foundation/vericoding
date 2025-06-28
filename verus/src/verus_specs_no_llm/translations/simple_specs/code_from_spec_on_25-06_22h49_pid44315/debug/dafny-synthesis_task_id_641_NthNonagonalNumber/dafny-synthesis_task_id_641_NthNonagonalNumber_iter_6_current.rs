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
        // Algebraic simplification
        assert(seven_n == 7 * n);
        assert(inner == seven_n - 5);
        assert(inner == 7 * n - 5);
        assert(product == n * inner);
        assert(product == n * (7 * n - 5));
        
        // We need to prove that n * (7*n - 5) is always even for n >= 0
        // We'll use the fact that either n is even or (7*n - 5) is even
        
        // For any integer n, we have n * (7*n - 5) = 7*n^2 - 5*n = n*(7*n - 5)
        // Let's prove this is always even by cases
        
        if n % 2 == 0 {
            // n is even, so n * anything is even
            // Since n is even, product = n * (7*n - 5) is even
            assert(product % 2 == 0);
        } else {
            // n is odd (n % 2 == 1)
            // When n is odd: 7*n is odd (odd * odd = odd)
            // So 7*n - 5 is even (odd - odd = even, since 5 is odd)
            // Therefore n * (7*n - 5) = odd * even = even
            assert(product % 2 == 0);
        }
        
        // Since product is even and Verus can verify integer division for even numbers
        assert(result == product / 2);
        assert(result == n * (7 * n - 5) / 2);
    }
    
    result
}

}