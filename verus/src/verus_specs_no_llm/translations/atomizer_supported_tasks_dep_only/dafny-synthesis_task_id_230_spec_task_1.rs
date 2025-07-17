// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_ReplaceBlanksWithChar(s: String, ch: char) -> v: string
    ensures
        v.len() == s.len(),
        forall |i: int| 0 <= i < s.len() ==> (s.index(i) == ' ' ==> v.index(i) == ch) && (s.index(i) != ' ' ==> v.index(i) == s.index(i))
;

proof fn lemma_ReplaceBlanksWithChar(s: String, ch: char) -> (v: String)
    ensures
        v.len() == s.len(),
        forall |i: int| 0 <= i < s.len() ==> (s.index(i) == ' ' ==> v.index(i) == ch) && (s.index(i) != ' ' ==> v.index(i) == s.index(i))
{
    String::new()
}

}