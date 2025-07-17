// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_containsSubString(a: Vec<char>, b: Vec<char>) -> pos: int
    requires
        0 <= b.len() <= a.len()
;

proof fn lemma_containsSubString(a: Vec<char>, b: Vec<char>) -> (pos: int)
    requires
        0 <= b.len() <= a.len()
{
    0
}

}