// ATOM 
predicate quickSorted(Seq: seq<int>)
{
  forall idx_1, idx_2 :: 0 <= idx_1 < idx_2 < |Seq| ==> Seq[idx_1] <= Seq[idx_2]
}

// IMPL 
method threshold(thres:int,Seq:seq<int>) returns (Seq_1:seq<int>,Seq_2:seq<int>)
  ensures (forall x | x in Seq_1 :: x <= thres) && (forall x | x in Seq_2 :: x >= thres)
  ensures |Seq_1| + |Seq_2| == |Seq| 
  ensures multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
{
  Seq_1 := [];
  Seq_2 := [];
  
  var i := 0;
  while i < |Seq|
    invariant 0 <= i <= |Seq|
    invariant forall x | x in Seq_1 :: x <= thres
    invariant forall x | x in Seq_2 :: x >= thres
    invariant |Seq_1| + |Seq_2| == i
    invariant multiset(Seq_1) + multiset(Seq_2) == multiset(Seq[..i])
  {
    if Seq[i] <= thres {
      Seq_1 := Seq_1 + [Seq[i]];
    } else {
      Seq_2 := Seq_2 + [Seq[i]];
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): Added assertion to help prove final postcondition */
  assert Seq[..i] == Seq;
}

// ATOM 
lemma Lemma_1(Seq_1:seq<int>,Seq_2:seq<int>)  // The proof of the lemma is not necessary
  requires multiset(Seq_1) == multiset(Seq_2)
  ensures forall x | x in Seq_1 :: x in Seq_2

{
  forall x | x in Seq_1
    ensures x in multiset(Seq_1)
  {
    var i := 0;
    while (i < |Seq_1|)
    {
      i := i + 1;
    }
  }

}

// IMPL 
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
    
    /* code modified by LLM (iteration 1): Strengthened termination reasoning */
    assert |smaller| + |larger| == |rest| == |Seq| - 1;
    assert |smaller| < |Seq| && |larger| < |Seq|;
    
    var sortedSmaller := quickSort(smaller);
    var sortedLarger := quickSort(larger);
    
    Seq' := sortedSmaller + [pivot] + sortedLarger;
    
    /* code modified by LLM (iteration 1): Simplified and strengthened multiset equality proof */
    assert multiset(smaller) + multiset(larger) == multiset(rest);
    assert multiset(rest) + multiset([pivot]) == multiset(Seq);
    
    calc {
      multiset(Seq');
      == multiset(sortedSmaller + [pivot] + sortedLarger);
      == multiset(sortedSmaller) + multiset([pivot]) + multiset(sortedLarger);
      == multiset(smaller) + multiset([pivot]) + multiset(larger);
      == multiset(smaller) + multiset(larger) + multiset([pivot]);
      == multiset(rest) + multiset([pivot]);
      == multiset(Seq);
    }
  }
}