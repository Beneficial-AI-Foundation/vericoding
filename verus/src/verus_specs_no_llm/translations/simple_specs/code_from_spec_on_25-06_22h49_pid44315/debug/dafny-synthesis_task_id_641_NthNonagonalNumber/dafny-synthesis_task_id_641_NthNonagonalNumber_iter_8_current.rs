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
        // Establish the algebraic equalities step by step
        assert(seven_n == 7 * n);
        assert(inner == seven_n - 5);
        assert(inner == 7 * n - 5);
        assert(product == n * inner);
        assert(product == n * (7 * n - 5));
        
        // For the division to work correctly in integer arithmetic,
        // we need to ensure that n * (7*n - 5) is always even when n >= 0.
        // We can prove this by considering the expression modulo 2.
        
        // Key insight: n * (7*n - 5) = 7*n^2 - 5*n
        // Let's analyze this modulo 2:
        // - If n is even (n ≡ 0 mod 2): 7*n^2 - 5*n ≡ 0 - 0 ≡ 0 mod 2
        // - If n is odd (n ≡ 1 mod 2): 7*n^2 - 5*n ≡ 7*1 - 5*1 ≡ 7 - 5 ≡ 2 ≡ 0 mod 2
        
        // In Verus, we can use the fact that integer division is well-defined
        // when the numerator is divisible by the denominator
        
        // The key insight is that for any integer n:
        // n * (7*n - 5) = n * 7*n - n * 5 = 7*n^2 - 5*n = n*(7*n - 5)
        // This expression is always even, so division by 2 is exact
        
        assert(result == product / 2);
        assert(product == n * (7 * n - 5));
        assert(result == n * (7 * n - 5) / 2);
    }
    
    result
}

}