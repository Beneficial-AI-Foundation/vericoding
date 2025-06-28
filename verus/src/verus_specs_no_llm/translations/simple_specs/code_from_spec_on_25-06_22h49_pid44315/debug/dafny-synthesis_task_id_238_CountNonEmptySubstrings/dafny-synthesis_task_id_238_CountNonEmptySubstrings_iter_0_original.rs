// Translated from Dafny
use builtin::*;
use builtin_macros::*;

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
    return 0;
}

}