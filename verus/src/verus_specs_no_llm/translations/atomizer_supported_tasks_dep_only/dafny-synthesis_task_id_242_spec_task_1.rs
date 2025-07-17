// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_CountCharacters(s: String) -> count: int
    ensures
        count >= 0,
        count == s.len()
;

proof fn lemma_CountCharacters(s: String) -> (count: int)
    ensures
        count >= 0,
        count == s.len()
{
    0
}

}