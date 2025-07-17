// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_IndexWiseAddition(a: Seq<Seq<int>>, b: Seq<Seq<int>>) -> result: seq<seq<int>>
    requires
        a.len() > 0 && b.len() > 0,
        a.len() == b.len(),
        forall |i: int| 0 <= i < a.len() ==> a.index(i).len() == b.index(i).len()
    ensures
        result.len() == a.len(),
        forall |i: int| 0 <= i < result.len() ==> result.index(i).len() == a.index(i).len(),
        forall |i: int| 0 <= i < result.len() ==> forall |j: int| 0 <= j < result.index(i).len() ==> result.index(i)[j] == a.index(i)[j] + b.index(i)[j]
;

proof fn lemma_IndexWiseAddition(a: Seq<Seq<int>>, b: Seq<Seq<int>>) -> (result: Seq<Seq<int>>)
    requires
        a.len() > 0 && b.len() > 0,
        a.len() == b.len(),
        forall |i: int| 0 <= i < a.len() ==> a.index(i).len() == b.index(i).len()
    ensures
        result.len() == a.len(),
        forall |i: int| 0 <= i < result.len() ==> result.index(i).len() == a.index(i).len(),
        forall |i: int| 0 <= i < result.len() ==> forall |j: int| 0 <= j < result.index(i).len() ==> result.index(i)[j] == a.index(i)[j] + b.index(i)[j]
{
    Seq::empty()
}

}