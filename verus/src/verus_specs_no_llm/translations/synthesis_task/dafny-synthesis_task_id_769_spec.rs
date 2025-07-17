// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Difference(a: Seq<int>, b: Seq<int>) -> diff: seq<int>
    ensures
        forall |x: int| x in diff <==> (x in a && x !in b),
        forall |i: int, j: int| 0 <= i < j < diff.len() ==> diff.index(i) != diff.index(j)
;

proof fn lemma_Difference(a: Seq<int>, b: Seq<int>) -> (diff: Seq<int>)
    ensures
        forall |x: int| x in diff <==> (x in a && x !in b),
        forall |i: int, j: int| 0 <= i < j < diff.len() ==> diff.index(i) != diff.index(j)
{
    Seq::empty()
}

}