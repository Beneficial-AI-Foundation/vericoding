// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_CountNonEmptySubstrings(s: String) -> count: int
    ensures
        count >= 0,
        count == (s.len() * (s.len() + 1)) / 2 // Formula for the number of non-empty substrings of a string
;

proof fn lemma_CountNonEmptySubstrings(s: String) -> (count: int)
    ensures
        count >= 0,
        count == (s.len() * (s.len() + 1)) / 2 // Formula for the number of non-empty substrings of a string
{
    0
}

}