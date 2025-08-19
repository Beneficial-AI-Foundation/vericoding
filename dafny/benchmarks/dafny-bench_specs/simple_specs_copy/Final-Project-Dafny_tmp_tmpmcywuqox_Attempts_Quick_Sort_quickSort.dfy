//ATOM

method threshold(thres:int,Seq:seq<int>) returns (Seq_1:seq<int>,Seq_2:seq<int>)
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



method quickSort(Seq: seq<int>) returns (Seq': seq<int>)
 ensures multiset(Seq) == multiset(Seq')
{
}
