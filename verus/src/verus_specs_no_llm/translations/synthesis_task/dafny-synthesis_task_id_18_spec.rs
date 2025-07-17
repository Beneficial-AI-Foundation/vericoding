// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_RemoveChars(s1: String, s2: String) -> v: string
    ensures
        v.len() <= s1.len(),
        forall |i: int| 0 <= i < v.len() ==> (v.index(i) in s1) && !(v.index(i) in s2),
        forall |i: int| 0 <= i < s1.len() ==> (s1.index(i) in s2) || (s1.index(i) in v)
;

proof fn lemma_RemoveChars(s1: String, s2: String) -> (v: String)
    ensures
        v.len() <= s1.len(),
        forall |i: int| 0 <= i < v.len() ==> (v.index(i) in s1) && !(v.index(i) in s2),
        forall |i: int| 0 <= i < s1.len() ==> (s1.index(i) in s2) || (s1.index(i) in v)
{
    String::new()
}

}