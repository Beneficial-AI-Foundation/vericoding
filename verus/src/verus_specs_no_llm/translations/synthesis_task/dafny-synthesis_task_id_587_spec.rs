// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_ArrayToSeq(a: Vec<int>) -> s: seq<int>
    requires
        a != null
    ensures
        s.len() == a.len(),
        forall |i: int| 0 <= i < a.len() ==> s.index(i) == a.index(i)
;

proof fn lemma_ArrayToSeq(a: Vec<int>) -> (s: Seq<int>)
    requires
        a != null
    ensures
        s.len() == a.len(),
        forall |i: int| 0 <= i < a.len() ==> s.index(i) == a.index(i)
{
    Seq::empty()
}

}