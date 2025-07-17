// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_ReplaceLastElement(first: Seq<int>, second: Seq<int>) -> result: seq<int>
    requires
        first.len() > 0
    ensures
        result.len() == first.len() - 1 + second.len(),
        forall |i: int| 0 <= i < first.len() - 1 ==> result.index(i) == first.index(i),
        forall |i: int| first.len() - 1 <= i < result.len() ==> result.index(i) == second.index(i - first.len() + 1)
;

proof fn lemma_ReplaceLastElement(first: Seq<int>, second: Seq<int>) -> (result: Seq<int>)
    requires
        first.len() > 0
    ensures
        result.len() == first.len() - 1 + second.len(),
        forall |i: int| 0 <= i < first.len() - 1 ==> result.index(i) == first.index(i),
        forall |i: int| first.len() - 1 <= i < result.len() ==> result.index(i) == second.index(i - first.len() + 1)
{
    Seq::empty()
}

}