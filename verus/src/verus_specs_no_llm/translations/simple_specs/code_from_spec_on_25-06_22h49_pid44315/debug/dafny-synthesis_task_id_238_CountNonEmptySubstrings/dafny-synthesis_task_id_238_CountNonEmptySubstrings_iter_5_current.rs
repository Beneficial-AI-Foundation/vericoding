use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CountNonEmptySubstrings(s: &str) -> (count: int)
    ensures
        count >= 0,
        count == (s.len() as int * (s.len() as int + 1)) / 2 // Formula for the number of non-empty substrings of a string
{
    let n = s.len() as int;
    let numerator = n * (n + 1);
    let result = numerator / 2;
    
    // Prove that the result is non-negative and matches the formula
    assert(result >= 0) by {
        assert(n >= 0) by {
            // Length is always non-negative
        };
        assert(n + 1 >= 1);
        assert(numerator >= 0) by {
            if n >= 0 {
                assert(n + 1 >= 1);
                assert(numerator == n * (n + 1) >= 0);
            }
        };
        assert(result >= 0) by {
            assert(numerator >= 0);
            assert(numerator / 2 >= 0);
        };
    };
    
    // Prove the division is exact (one of n or n+1 is even)
    assert(numerator % 2 == 0) by {
        // Either n is even or n+1 is even, so their product is even
        if n % 2 == 0 {
            // n is even, so n * (n+1) is even
            assert(numerator % 2 == 0);
        } else {
            // n is odd, so n+1 is even, so n * (n+1) is even
            assert((n + 1) % 2 == 0);
            assert(numerator % 2 == 0);
        }
    };
    
    result
}

}