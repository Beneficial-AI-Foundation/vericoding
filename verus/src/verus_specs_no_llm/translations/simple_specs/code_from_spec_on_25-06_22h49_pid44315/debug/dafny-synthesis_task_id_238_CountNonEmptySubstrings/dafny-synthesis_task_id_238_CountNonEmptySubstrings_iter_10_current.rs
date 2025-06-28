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
    
    // Prove that n >= 0 (sequence length is non-negative)
    assert(n >= 0);
    
    // Prove that numerator >= 0
    assert(numerator >= 0) by {
        assert(n >= 0);
        assert(n + 1 >= 1);
        // For non-negative n, n * (n+1) >= 0
        if n == 0 {
            assert(numerator == 0);
        } else {
            assert(n > 0);
            assert(n + 1 > 0);
            assert(numerator > 0);
        }
    };
    
    // Prove that the result is non-negative
    assert(result >= 0) by {
        assert(numerator >= 0);
        // Since numerator >= 0 and we're dividing by positive 2
        assert(2 > 0);
        assert(numerator / 2 >= 0);
    };
    
    // The key insight: for any integer n >= 0, either n or (n+1) is even
    // This means n * (n+1) is always even, so division by 2 gives integer result
    assert(numerator % 2 == 0) by {
        // Case analysis on whether n is even or odd
        if n % 2 == 0 {
            // n is even, so n = 2k for some k
            // Then n * (n+1) = 2k * (2k+1) which is divisible by 2
            assert(exists|k: int| n == 2 * k);
        } else {
            // n is odd, so n = 2k+1 for some k
            // Then n+1 = 2k+2 = 2(k+1) is even
            // So n * (n+1) = (2k+1) * 2(k+1) which is divisible by 2
            assert(n % 2 == 1);
            assert((n + 1) % 2 == 0);
            assert(exists|k: int| n + 1 == 2 * k);
        }
    };
    
    // Since numerator is even and non-negative, numerator/2 is an integer
    assert(result * 2 == numerator);
    
    result
}

}