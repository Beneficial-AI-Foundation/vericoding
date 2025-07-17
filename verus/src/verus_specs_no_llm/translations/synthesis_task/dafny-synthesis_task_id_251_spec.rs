// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_InsertBeforeEach(s: Seq<String>, x: String) -> v: seq<string>
    ensures
        v.len() == 2 * s.len(),
        forall |i: int| 0 <= i < s.len() ==> v.index(2*i) == x && v.index(2*i + 1) == s.index(i)
;

proof fn lemma_InsertBeforeEach(s: Seq<String>, x: String) -> (v: Seq<String>)
    ensures
        v.len() == 2 * s.len(),
        forall |i: int| 0 <= i < s.len() ==> v.index(2*i) == x && v.index(2*i + 1) == s.index(i)
{
    Seq::empty()
}

}