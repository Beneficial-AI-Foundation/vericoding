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
            // n is even, so n * anything is even
            assert(n == 2 * (n / 2));
            assert(product == 2 * (n / 2) * inner);
            assert(product % 2 == 0);
        } else {
            // n is odd
            assert(n % 2 == 1);
            // 7 is odd, so 7*n is odd when n is odd
            assert(seven_n % 2 == 1) by {
                assert(seven_n == 7 * n);
                assert(7 % 2 == 1);
                assert(n % 2 == 1);
                // odd * odd = odd
            };
            // 7*n - 5: odd - odd = even (since 5 is odd)
            assert(5 % 2 == 1);
            assert(inner % 2 == 0) by {
                assert(inner == seven_n - 5);
                assert(seven_n % 2 == 1);
                assert(5 % 2 == 1);
                // odd - odd = even
            };
            // n * inner: odd * even = even
            assert(product % 2 == 0) by {
                assert(product == n * inner);
                assert(n % 2 == 1);
                assert(inner % 2 == 0);
                assert(inner == 2 * (inner / 2));
                assert(product == n * 2 * (inner / 2));
                assert(product == 2 * (n * (inner / 2)));
            };
        }
        
        // Since product is even, product = 2 * (product / 2)
        assert(product % 2 == 0);
        assert(product == 2 * (product / 2));
        assert(result == product / 2);
        
        // Verify the final equation
        assert(product == n * (7 * n - 5)) by {
            assert(product == n * inner);
            assert(inner == seven_n - 5);
            assert(seven_n == 7 * n);
            assert(inner == 7 * n - 5);
        };
        
        assert(result == n * (7 * n - 5) / 2) by {
            assert(result == product / 2);
            assert(product == n * (7 * n - 5));
        };
    }
    
    result
}

}