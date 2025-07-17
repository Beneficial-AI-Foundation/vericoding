// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_SubtractSequences(a: Seq<int>, b: Seq<int>) -> result: seq<int>
    requires
        a.len() == b.len()
    ensures
        result.len() == a.len(),
        forall |i: int| 0 <= i < result.len() ==> result.index(i) == a.index(i) - b.index(i)
;

proof fn lemma_SubtractSequences(a: Seq<int>, b: Seq<int>) -> (result: Seq<int>)
    requires
        a.len() == b.len()
    ensures
        result.len() == a.len(),
        forall |i: int| 0 <= i < result.len() ==> result.index(i) == a.index(i) - b.index(i)
{
    Seq::empty()
}

}