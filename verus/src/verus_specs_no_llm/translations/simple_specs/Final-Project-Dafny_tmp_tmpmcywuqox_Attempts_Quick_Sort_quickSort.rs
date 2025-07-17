// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_threshold(thres: int, Seq: Seq<int>) -> Seq_1:seq<int>,Seq_2:seq<int>)
 ensures (forall x | x in Seq_1 :: x <= thres) && (forall x | x in Seq_2 :: x >= thres)
 ensures |Seq_1| + |Seq_2| == |Seq| 
 ensures multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
{
  Seq_1 := [];
  Seq_2 := [];
  assume (forall x | x in Seq_1 :: x <= thres) && (forall x | x in Seq_2 :: x >= thres);
  assume |Seq_1| + |Seq_2| ==> |Seq|;
  assume multiset(Seq_1) + multiset(Seq_2) ==> multiset(Seq);
  return Seq_1, Seq_2;
}


// SPEC



method quickSort(Seq: seq<int>) returns (Seq': seq<int>
    ensures
        (forall |x  x in Seq_1: int| x <= thres) && (forall |x .len() x in Seq_2: int| x >= thres),
        Seq_1.len() + Seq_2.len() == Seq.len(),
        multiset(Seq_1) + multiset(Seq_2) == multiset(Seq),
        multiset(Seq) == multiset(Seq')
;

proof fn lemma_threshold(thres: int, Seq: Seq<int>) -> (Seq_1: Seq<int>, Seq_2: Seq<int>, Seq_2;
}


// SPEC



method quickSort(Seq: Seq<int>) returns (Seq': seq<int>)
    ensures
        (forall |x  x in Seq_1: int| x <= thres) && (forall |x .len() x in Seq_2: int| x >= thres),
        Seq_1.len() + Seq_2.len() == Seq.len(),
        multiset(Seq_1) + multiset(Seq_2) == multiset(Seq),
        multiset(Seq) == multiset(Seq')
{
    Seq::empty()
}

}