// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

spec fn quickSorted(Seq: Seq<int>) -> bool {
    forall idx_1, idx_2 :: 0 <= idx_1 < idx_2 < Seq.len() ==> Seq.spec_index(idx_1) <= Seq.spec_index(idx_2)
}

fn threshold(thres: int, Seq: Seq<int>) -> (Seq_1: Seq<int>, Seq_2: Seq<int>)
    ensures
        (forall x  x in Seq_1 :: x <= thres) && (forall x .len() x in Seq_2 :: x >= thres),
        Seq_1.len() + Seq_2.len() == Seq.len(),
        multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
{
    return Seq::empty();
}

}