//ATOM
method threshold(thres:int,Seq:seq<int>) returns (Seq_1:seq<int>,Seq_2:seq<int>)
 ensures (forall x | x in Seq_1 :: x <= thres) && (forall x | x in Seq_2 :: x >= thres)
 ensures |Seq_1| + |Seq_2| == |Seq| 
 ensures multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
{
}

//IMPL quickSort
method quickSort(Seq: seq<int>) returns (Seq': seq<int>)
 ensures multiset(Seq) == multiset(Seq')
 decreases |Seq|
{
  if |Seq| <= 1 {
    Seq' := Seq;
  } else {
    var pivot := Seq[0];
    var rest := Seq[1..];
    var smaller, larger := threshold(pivot, rest);
    
    /* code modified by LLM (iteration 1): Added termination proof using threshold postconditions */
    assert |smaller| + |larger| == |rest| by {
      assert multiset(smaller) + multiset(larger) == multiset(rest);
    }
    assert |rest| == |Seq| - 1;
    assert |smaller| < |Seq| && |larger| < |Seq|;
    
    var sortedSmaller := quickSort(smaller);
    var sortedLarger := quickSort(larger);
    
    Seq' := sortedSmaller + [pivot] + sortedLarger;
    
    /* code modified by LLM (iteration 1): Restructured multiset equality proof with explicit lemma calls */
    calc {
      multiset(Seq');
      == multiset(sortedSmaller + [pivot] + sortedLarger);
      == multiset(sortedSmaller) + multiset([pivot]) + multiset(sortedLarger);
      == { assert multiset(sortedSmaller) == multiset(smaller); }
         multiset(smaller) + multiset([pivot]) + multiset(larger);
      == { assert multiset(smaller) + multiset(larger) == multiset(rest); }
         multiset(rest) + multiset([pivot]);
      == { assert rest == Seq[1..] && pivot == Seq[0]; }
         multiset(Seq[1..]) + multiset([Seq[0]]);
      == multiset(Seq);
    }
  }
}