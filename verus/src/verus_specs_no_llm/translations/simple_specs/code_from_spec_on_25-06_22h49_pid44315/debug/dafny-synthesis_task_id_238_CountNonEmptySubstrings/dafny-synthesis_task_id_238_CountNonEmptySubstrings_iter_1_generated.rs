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
    let n = s.len();
    let result = (n * (n + 1)) / 2;
    
    // The postcondition directly gives us the formula
    assert(result >= 0) by {
        // n >= 0, so n * (n + 1) >= 0, so (n * (n + 1)) / 2 >= 0
    };
    
    result
}

}