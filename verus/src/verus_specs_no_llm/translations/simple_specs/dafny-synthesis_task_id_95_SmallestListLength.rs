// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_SmallestListLength(s: Seq<Seq<int>>) -> v: int
    requires
        s.len() > 0
    ensures
        forall |i: int| 0 <= i < s.len() ==> v <= s.index(i).len(),
        exists |i: int| 0 <= i < s.len() && v == s.index(i).len()
;

proof fn lemma_SmallestListLength(s: Seq<Seq<int>>) -> (v: int)
    requires
        s.len() > 0
    ensures
        forall |i: int| 0 <= i < s.len() ==> v <= s.index(i).len(),
        exists |i: int| 0 <= i < s.len() && v == s.index(i).len()
{
    0
}

}