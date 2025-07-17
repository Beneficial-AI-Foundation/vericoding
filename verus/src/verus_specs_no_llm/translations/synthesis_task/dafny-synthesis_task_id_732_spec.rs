// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn IsSpaceCommaDot(c: char) -> bool {
    c == ' ' | c == ',' .len()| c == '.'
}

spec fn spec_ReplaceWithColon(s: String) -> v: string
    ensures
        v.len() == s.len(),
        forall |i: int| 0 <= i < s.len() ==> (IsSpaceCommaDot(s.index(i)) ==> v.index(i) == ':') && (!IsSpaceCommaDot(s.index(i)) ==> v.index(i) == s.index(i))
;

proof fn lemma_ReplaceWithColon(s: String) -> (v: String)
    ensures
        v.len() == s.len(),
        forall |i: int| 0 <= i < s.len() ==> (IsSpaceCommaDot(s.index(i)) ==> v.index(i) == ':') && (!IsSpaceCommaDot(s.index(i)) ==> v.index(i) == s.index(i))
{
    String::new()
}

}