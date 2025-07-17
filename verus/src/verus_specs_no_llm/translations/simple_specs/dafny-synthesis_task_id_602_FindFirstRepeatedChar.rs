// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_FindFirstRepeatedChar(s: String) -> found: bool, c: char
    ensures
        found ==> exists |i: int, j: int| 0 <= i < j < s.len() && s.index(i) == s.index(j) && s.index(i) == c && (forall |k: int, l: int| 0 <= k < l < j && s.index(k) == s.index(l) ==> k >= i),
        !found ==> (forall |i: int, j: int| 0 <= i < j < s.len() ==> s.index(i) != s.index(j))
;

proof fn lemma_FindFirstRepeatedChar(s: String) -> (found: bool, c: char)
    ensures
        found ==> exists |i: int, j: int| 0 <= i < j < s.len() && s.index(i) == s.index(j) && s.index(i) == c && (forall |k: int, l: int| 0 <= k < l < j && s.index(k) == s.index(l) ==> k >= i),
        !found ==> (forall |i: int, j: int| 0 <= i < j < s.len() ==> s.index(i) != s.index(j))
{
    (false, '\0')
}

}