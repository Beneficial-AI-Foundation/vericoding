// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn threshold(thres: int, Seq: Seq<int>) -> (Seq_1: Seq<int>, Seq_2: Seq<int>, Seq_2;
}


// SPEC



method quickSort(Seq: Seq<int>) returns (Seq': seq<int>)
    ensures
        (forall x  x in Seq_1 :: x <= thres) && (forall x .len() x in Seq_2 :: x >= thres),
        Seq_1.len() + Seq_2.len() == Seq.len(),
        multiset(Seq_1) + multiset(Seq_2) == multiset(Seq),
        multiset(Seq) == multiset(Seq')
{
    return Seq::empty();
}

}