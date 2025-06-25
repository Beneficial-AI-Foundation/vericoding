// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn CountNonEmptySubstrings(s: String) -> (count: int)
    ensures count >= 0,
            count == (s.len() * (s.len() + 1)) / 2 // Formula for the number of non-empty substrings of a string
{
}

}