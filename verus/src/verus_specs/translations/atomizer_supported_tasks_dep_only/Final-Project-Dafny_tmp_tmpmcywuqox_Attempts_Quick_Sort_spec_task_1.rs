use vstd::prelude::*;

pub fn threshold(thres: int, Seq: Seq<int>) -> (Seq_1: Seq<int>, Seq_2: Seq<int>)
    ensures
        (forall|x: int| Seq_1.contains(x) ==> x <= thres) && (forall|x: int| Seq_2.contains(x) ==> x >= thres),
        Seq_1.len() + Seq_2.len() == Seq.len(),
        Seq_1.to_multiset().add(Seq_2.to_multiset()) == Seq.to_multiset(),
{
}