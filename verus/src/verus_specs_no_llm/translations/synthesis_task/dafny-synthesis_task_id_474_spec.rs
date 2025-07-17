// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_ReplaceChars(s: String, oldChar: char, newChar: char) -> v: string
    ensures
        v.len() == s.len(),
        forall |i: int| 0 <= i < s.len() ==> (s.index(i) == oldChar ==> v.index(i) == newChar) && (s.index(i) != oldChar ==> v.index(i) == s.index(i))
;

proof fn lemma_ReplaceChars(s: String, oldChar: char, newChar: char) -> (v: String)
    ensures
        v.len() == s.len(),
        forall |i: int| 0 <= i < s.len() ==> (s.index(i) == oldChar ==> v.index(i) == newChar) && (s.index(i) != oldChar ==> v.index(i) == s.index(i))
{
    String::new()
}

}