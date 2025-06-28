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
        assert(n * (n + 1) >= 0);
    };
    
    // Prove that the result is non-negative
    assert(result >= 0) by {
        assert(numerator >= 0);
        // For non-negative integers, division by positive number gives non-negative result
        assert(numerator / 2 >= 0);
    };
    
    // The key insight: for any integer n >= 0, either n or (n+1) is even
    // This means n * (n+1) is always even, so division by 2 is exact
    assert(numerator % 2 == 0) by {
        if n % 2 == 0 {
            // n is even, so n * (n+1) is even
            assert(numerator % 2 == 0);
        } else {
            // n is odd, so (n+1) is even, making n * (n+1) even
            assert(n % 2 == 1);
            assert((n + 1) % 2 == 0);
            assert(numerator % 2 == 0);
        }
    };
    
    result
}

}