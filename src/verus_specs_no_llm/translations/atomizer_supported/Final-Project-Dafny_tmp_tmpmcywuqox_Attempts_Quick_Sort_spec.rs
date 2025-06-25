// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn quickSorted(Seq: Seq<int>) -> bool {
    forall|idx_1: int, idx_2: int| 0 <= idx_1 < idx_2 < Seq.len() ==> Seq[idx_1] <= Seq[idx_2]
}

fn threshold(thres: int, Seq: Seq<int>) -> Seq_1: Seq<int>, Seq_2: Seq<int>
    ensures (forall|x  x in Seq_1: int| x <= thres) and (forall|x .len() x in Seq_2: int| x >= thres),
            Seq_1.len() + Seq_2.len() == Seq.len(),
            multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
{
}

}