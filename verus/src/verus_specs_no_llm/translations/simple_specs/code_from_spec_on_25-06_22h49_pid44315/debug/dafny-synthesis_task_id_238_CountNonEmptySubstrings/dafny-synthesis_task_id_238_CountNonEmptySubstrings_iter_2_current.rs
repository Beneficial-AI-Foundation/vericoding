use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CountNonEmptySubstrings(s: String) -> (count: int)
    ensures
        count >= 0,
        count == (s.len() * (s.len() + 1)) / 2 // Formula for the number of non-empty substrings of a string
{
    let n = s.len() as int;
    let result = (n * (n + 1)) / 2;
    
    // Prove that the result is non-negative
    assert(result >= 0) by {
        assert(n >= 0);
        assert(n + 1 >= 1);
        assert(n * (n + 1) >= 0);
        assert((n * (n + 1)) / 2 >= 0);
    };
    
    // Prove that the result matches the formula
    assert(result == (s.len() * (s.len() + 1)) / 2) by {
        assert(n == s.len());
        assert(result == (n * (n + 1)) / 2);
        assert((n * (n + 1)) / 2 == (s.len() * (s.len() + 1)) / 2);
    };
    
    result
}

}