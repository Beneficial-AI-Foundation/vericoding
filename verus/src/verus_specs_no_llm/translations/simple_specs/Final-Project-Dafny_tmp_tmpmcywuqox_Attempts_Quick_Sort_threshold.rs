// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_threshold(thres: int, Seq: Seq<int>) -> Seq_1:seq<int>,Seq_2:seq<int>
    ensures
        (forall |x  x in Seq_1: int| x <= thres) && (forall |x .len() x in Seq_2: int| x >= thres),
        Seq_1.len() + Seq_2.len() == Seq.len(),
        multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
;

proof fn lemma_threshold(thres: int, Seq: Seq<int>) -> (Seq_1: Seq<int>, Seq_2: Seq<int>)
    ensures
        (forall |x  x in Seq_1: int| x <= thres) && (forall |x .len() x in Seq_2: int| x >= thres),
        Seq_1.len() + Seq_2.len() == Seq.len(),
        multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
{
    Seq::empty()
}

}