// IMPL quickSort
method quickSort(Seq: seq<int>) returns (Seq': seq<int>)
  ensures multiset(Seq) == multiset(Seq')
  decreases |Seq|
{
  if |Seq| <= 1 {
    Seq' := Seq;
  } else {
    var pivot := Seq[0];
    var less := [];
    var greater := [];
    
    var i := 1;
    while i < |Seq|
      invariant 1 <= i <= |Seq|
      invariant multiset(less) + multiset(greater) == multiset(Seq[1..i])
    {
      if Seq[i] <= pivot {
        less := less + [Seq[i]];
      } else {
        greater := greater + [Seq[i]];
      }
      i := i + 1;
    }
    
    var sortedLess := quickSort(less);
    var sortedGreater := quickSort(greater);
    
    Seq' := sortedLess + [pivot] + sortedGreater;
    
    /* code modified by LLM (iteration 1): added comprehensive multiset equality proof */
    assert i == |Seq|;
    assert Seq[1..i] == Seq[1..];
    assert multiset(less) + multiset(greater) == multiset(Seq[1..]);
    assert multiset(sortedLess) == multiset(less);
    assert multiset(sortedGreater) == multiset(greater);
    assert multiset(Seq') == multiset(sortedLess) + multiset([pivot]) + multiset(sortedGreater);
    assert multiset(Seq') == multiset(less) + multiset([pivot]) + multiset(greater);
    assert multiset(Seq') == multiset([pivot]) + multiset(less) + multiset(greater);
    assert multiset(Seq') == multiset([pivot]) + multiset(Seq[1..]);
    assert multiset(Seq) == multiset([Seq[0]]) + multiset(Seq[1..]);
    assert multiset([pivot]) == multiset([Seq[0]]);
  }
}

// IMPL threshold
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
    invariant (forall x | x in Seq_1 :: x <= thres)
    invariant (forall x | x in Seq_2 :: x >= thres)
    invariant |Seq_1| + |Seq_2| == i
    invariant multiset(Seq_1) + multiset(Seq_2) == multiset(Seq[..i])
  {
    /* code modified by LLM (iteration 1): added sequence slicing and multiset preservation proofs */
    assert Seq[..i+1] == Seq[..i] + [Seq[i]];
    
    if Seq[i] <= thres {
      /* code modified by LLM (iteration 1): store old values for proof */
      var oldSeq_1 := Seq_1;
      Seq_1 := Seq_1 + [Seq[i]];
      assert multiset(Seq_1) == multiset(oldSeq_1) + multiset([Seq[i]]);
      assert multiset(Seq_1) + multiset(Seq_2) == multiset(oldSeq_1) + multiset([Seq[i]]) + multiset(Seq_2);
      assert multiset(oldSeq_1) + multiset(Seq_2) == multiset(Seq[..i]);
      assert multiset(Seq_1) + multiset(Seq_2) == multiset(Seq[..i]) + multiset([Seq[i]]);
      assert multiset(Seq_1) + multiset(Seq_2) == multiset(Seq[..i+1]);
    } else {
      /* code modified by LLM (iteration 1): store old values for proof */
      var oldSeq_2 := Seq_2;
      Seq_2 := Seq_2 + [Seq[i]];
      assert multiset(Seq_2) == multiset(oldSeq_2) + multiset([Seq[i]]);
      assert multiset(Seq_1) + multiset(Seq_2) == multiset(Seq_1) + multiset(oldSeq_2) + multiset([Seq[i]]);
      assert multiset(Seq_1) + multiset(oldSeq_2) == multiset(Seq[..i]);
      assert multiset(Seq_1) + multiset(Seq_2) == multiset(Seq[..i]) + multiset([Seq[i]]);
      assert multiset(Seq_1) + multiset(Seq_2) == multiset(Seq[..i+1]);
    }
    i := i + 1;
  }
  
  /* code modified by LLM (iteration 1): added final proof that complete sequence equals original */
  assert i == |Seq|;
  assert Seq[..i] == Seq;
}

// ATOM 
lemma Lemma_1(Seq_1:seq,Seq_2:seq)  // The proof of the lemma is not necessary
  requires multiset(Seq_1) == multiset(Seq_2)
  ensures forall x | x in Seq_1 :: x in Seq_2
{
}