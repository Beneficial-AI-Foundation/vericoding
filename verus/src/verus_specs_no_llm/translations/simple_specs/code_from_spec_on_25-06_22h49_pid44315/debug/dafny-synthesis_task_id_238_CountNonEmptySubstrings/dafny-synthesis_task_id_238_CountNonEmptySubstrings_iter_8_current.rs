use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CountNonEmptySubstrings(s: Seq<char>) -> (count: int)
    ensures
        count >= 0,
        count == (s.len() as int * (s.len() as int + 1)) / 2 // Formula for the number of non-empty substrings of a string
{
    let n = s.len() as int;
    let numerator = n * (n + 1);
    let result = numerator / 2;
    
    // Prove that the result is non-negative
    assert(result >= 0) by {
        assert(n >= 0);
        assert(n + 1 >= 1);
        // Since n >= 0 and n + 1 >= 1, their product is >= 0
        assert(numerator >= 0);
        // Division of non-negative by positive gives non-negative
        assert(numerator / 2 >= 0);
    };
    
    // Prove the division works correctly by cases
    assert(numerator % 2 == 0) by {
        // Either n is even or n is odd
        if n % 2 == 0 {
            // n is even: n = 2k for some k
            // numerator = n * (n+1) = 2k * (2k+1) = 2 * k * (2k+1)
            // So numerator is divisible by 2
            assert(numerator % 2 == 0) by {
                // n is even, so n is divisible by 2
                // Therefore n * (n+1) is divisible by 2
                assert(n % 2 == 0);
            };
        } else {
            // n is odd: n = 2k+1 for some k
            // n+1 = 2k+2 = 2(k+1), so n+1 is even
            // numerator = n * (n+1) = (2k+1) * 2(k+1) = 2 * (2k+1) * (k+1)
            // So numerator is divisible by 2
            assert(n % 2 == 1);
            assert((n + 1) % 2 == 0) by {
                // If n is odd, then n+1 is even
                assert(n % 2 == 1);
            };
            assert(numerator % 2 == 0) by {
                // Since n+1 is even, n * (n+1) is even
                assert((n + 1) % 2 == 0);
            };
        }
    };
    
    // The postcondition follows directly from our definitions
    assert(result == numerator / 2);
    assert(numerator == n * (n + 1));
    
    result
}

}