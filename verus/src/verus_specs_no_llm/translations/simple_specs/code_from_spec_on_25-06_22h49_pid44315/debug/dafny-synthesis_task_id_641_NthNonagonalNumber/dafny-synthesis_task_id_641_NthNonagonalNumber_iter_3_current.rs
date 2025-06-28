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
    let result = n * (7 * n - 5) / 2;
    
    proof {
        // We need to prove that n * (7 * n - 5) is always even
        // This ensures that the division by 2 is exact
        if n % 2 == 0 {
            // n is even, so n * (7 * n - 5) is even
            assert(n * (7 * n - 5) % 2 == 0);
        } else {
            // n is odd, so 7*n is odd, so 7*n - 5 is even
            assert((7 * n) % 2 == 1); // 7*n is odd when n is odd
            assert((7 * n - 5) % 2 == 0); // odd - odd = even
            assert(n * (7 * n - 5) % 2 == 0); // odd * even = even
        }
        
        // Since n * (7 * n - 5) is even, division by 2 is exact
        assert(n * (7 * n - 5) == 2 * (n * (7 * n - 5) / 2));
    }
    
    result
}

}