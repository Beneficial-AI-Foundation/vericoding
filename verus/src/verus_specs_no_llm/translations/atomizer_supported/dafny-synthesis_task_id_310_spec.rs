// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_ToCharArray(s: String) -> a: array<char>
    ensures
        a.len() == s.len(),
        forall |i: int| 0 <= i < s.len() ==> a.index(i) == s.index(i)
;

proof fn lemma_ToCharArray(s: String) -> (a: Vec<char>)
    ensures
        a.len() == s.len(),
        forall |i: int| 0 <= i < s.len() ==> a.index(i) == s.index(i)
{
    Vec::new()
}

}