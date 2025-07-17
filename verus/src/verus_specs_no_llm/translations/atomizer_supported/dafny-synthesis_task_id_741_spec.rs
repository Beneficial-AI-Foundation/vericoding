// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_AllCharactersSame(s: String) -> result: bool
    ensures
        result ==> forall |i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s.index(i) == s.index(j),
        !result ==> (s.len() > 1) && (exists |i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s.index(i) != s.index(j))
;

proof fn lemma_AllCharactersSame(s: String) -> (result: bool)
    ensures
        result ==> forall |i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() ==> s.index(i) == s.index(j),
        !result ==> (s.len() > 1) && (exists |i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j && s.index(i) != s.index(j))
{
    false
}

}