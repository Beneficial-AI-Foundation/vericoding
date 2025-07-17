// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_AppendArrayToSeq(s: Seq<int>, a: Vec<int>) -> r: seq<int>
    requires
        a != null
    ensures
        r.len() == s.len() + a.len(),
        forall |i: int| 0 <= i < s.len() ==> r.index(i) == s.index(i),
        forall |i: int| 0 <= i < a.len() ==> r.index(s.len() + i) == a.index(i)
;

proof fn lemma_AppendArrayToSeq(s: Seq<int>, a: Vec<int>) -> (r: Seq<int>)
    requires
        a != null
    ensures
        r.len() == s.len() + a.len(),
        forall |i: int| 0 <= i < s.len() ==> r.index(i) == s.index(i),
        forall |i: int| 0 <= i < a.len() ==> r.index(s.len() + i) == a.index(i)
{
    Seq::empty()
}

}