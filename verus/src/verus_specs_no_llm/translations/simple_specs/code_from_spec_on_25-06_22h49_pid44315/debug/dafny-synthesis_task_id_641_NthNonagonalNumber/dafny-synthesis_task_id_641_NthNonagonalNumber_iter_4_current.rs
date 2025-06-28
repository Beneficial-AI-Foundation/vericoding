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
        // We need to prove that n * (7*n - 5) is always even
        // Case analysis on n modulo 2
        if n % 2 == 0 {
            // n is even
            // n * (7*n - 5) = even * anything = even
            assert(product % 2 == 0);
        } else {
            // n is odd
            // 7*n is odd (odd * odd = odd)
            // 7*n - 5 is even (odd - odd = even)  
            // n * (7*n - 5) = odd * even = even
            assert(seven_n % 2 == 1);
            assert(inner % 2 == 0);
            assert(product % 2 == 0);
        }
        
        // Since product is even, division by 2 is exact
        assert(product == 2 * result);
        assert(result == product / 2);
        assert(result == n * (7 * n - 5) / 2);
    }
    
    result
}

}