// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn threshold(thres: int, Seq: Seq<int>) -> Seq_1: Seq<int>, Seq_2: Seq<int>
    ensures (forall|x  x in Seq_1: int| x <= thres) and (forall|x .len() x in Seq_2: int| x >= thres),
            Seq_1.len() + Seq_2.len() == Seq.len(),
            multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
{
}

}