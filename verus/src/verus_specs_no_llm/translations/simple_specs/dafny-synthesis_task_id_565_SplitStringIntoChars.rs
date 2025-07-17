// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_SplitStringIntoChars(s: String) -> v: seq<char>
    ensures
        v.len() == s.len(),
        forall |i: int| 0 <= i < s.len() ==> v.index(i) == s.index(i)
;

proof fn lemma_SplitStringIntoChars(s: String) -> (v: Seq<char>)
    ensures
        v.len() == s.len(),
        forall |i: int| 0 <= i < s.len() ==> v.index(i) == s.index(i)
{
    Seq::empty()
}

}