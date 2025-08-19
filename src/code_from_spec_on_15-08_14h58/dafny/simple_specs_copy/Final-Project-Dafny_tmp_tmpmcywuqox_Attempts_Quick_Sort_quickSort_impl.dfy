//ATOM

method threshold(thres:int,Seq:seq<int>) returns (Seq_1:seq<int>,Seq_2:seq<int>)
 ensures (forall x | x in Seq_1 :: x <= thres) && (forall x | x in Seq_2 :: x >= thres)
 ensures |Seq_1| + |Seq_2| == |Seq| 
 ensures multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
{
  Seq_1 := [];
  Seq_2 := [];
  /* code modified by LLM (iteration 2): Fixed loop invariants and added proof steps */
  for i := 0 to |Seq|
    invariant |Seq_1| + |Seq_2| == i
    invariant forall x | x in Seq_1 :: x <= thres
    invariant forall x | x in Seq_2 :: x >= thres
    invariant multiset(Seq_1) + multiset(Seq_2) == multiset(Seq[0..i])
  {
    /* code modified by LLM (iteration 2): Added assertions to help prove invariant maintenance */
    assert Seq[0..i+1] == Seq[0..i] + [Seq[i]];
    assert multiset(Seq[0..i+1]) == multiset(Seq[0..i]) + multiset([Seq[i]]);
    
    if Seq[i] <= thres {
      Seq_1 := Seq_1 + [Seq[i]];
      /* code modified by LLM (iteration 2): Prove multiset equality after update */
      assert multiset(Seq_1) == multiset(old(Seq_1)) + multiset([Seq[i]]);
      assert multiset(Seq_1) + multiset(Seq_2) == multiset(old(Seq_1)) + multiset([Seq[i]]) + multiset(Seq_2);
      assert multiset(Seq_1) + multiset(Seq_2) == multiset(Seq[0..i]) + multiset([Seq[i]]);
      assert multiset(Seq_1) + multiset(Seq_2) == multiset(Seq[0..i+1]);
    } else {
      Seq_2 := Seq_2 + [Seq[i]];
      /* code modified by LLM (iteration 2): Prove multiset equality after update */
      assert multiset(Seq_2) == multiset(old(Seq_2)) + multiset([Seq[i]]);
      assert multiset(Seq_1) + multiset(Seq_2) == multiset(Seq_1) + multiset(old(Seq_2)) + multiset([Seq[i]]);
      assert multiset(Seq_1) + multiset(Seq_2) == multiset(Seq[0..i]) + multiset([Seq[i]]);
      assert multiset(Seq_1) + multiset(Seq_2) == multiset(Seq[0..i+1]);
    }
  }
  /* code modified by LLM (iteration 2): Final assertion to prove postcondition */
  assert Seq[0..|Seq|] == Seq;
  assert multiset(Seq_1) + multiset(Seq_2) == multiset(Seq[0..|Seq|]);
  return Seq_1, Seq_2;
}

/* code modified by LLM (iteration 3): Added helper lemma for multiset properties */
lemma MultisetConcatenation(a: seq<int>, b: seq<int>, c: seq<int>)
  ensures multiset(a + b + c) == multiset(a) + multiset(b) + multiset(c)
{
}

/* code modified by LLM (iteration 3): Fixed helper lemma for sequence slicing */
lemma SequenceSlicing(s: seq<int>)
  requires |s| > 0
  ensures multiset(s) == multiset(s[0..1]) + multiset(s[1..])
{
  /* code modified by LLM (iteration 3): Added proof body */
  assert s == s[0..1] + s[1..];
  assert s[0..1] == [s[0]];
  assert multiset(s) == multiset(s[0..1] + s[1..]);
  assert multiset(s[0..1] + s[1..]) == multiset(s[0..1]) + multiset(s[1..]);
}

//IMPL 

method quickSort(Seq: seq<int>) returns (Seq': seq<int>)
 ensures multiset(Seq) == multiset(Seq')
 decreases |Seq|
{
  if |Seq| <= 1 {
    Seq' := Seq;
  } else {
    var pivot := Seq[0];
    /* code modified by LLM (iteration 2): Create proper partitions excluding the pivot to ensure termination */
    var remaining := Seq[1..];
    var left, right := threshold(pivot, remaining);
    var sortedLeft := quickSort(left);
    var sortedRight := quickSort(right);
    /* code modified by LLM (iteration 2): Include pivot in the result between left and right partitions */
    Seq' := sortedLeft + [pivot] + sortedRight;
    
    /* code modified by LLM (iteration 3): Added comprehensive proof annotations */
    MultisetConcatenation(sortedLeft, [pivot], sortedRight);
    assert multiset(Seq') == multiset(sortedLeft) + multiset([pivot]) + multiset(sortedRight);
    assert multiset(sortedLeft) == multiset(left);
    assert multiset(sortedRight) == multiset(right);
    assert multiset(left) + multiset(right) == multiset(remaining);
    SequenceSlicing(Seq);
    assert multiset([pivot]) == multiset(Seq[0..1]);
    assert multiset(remaining) == multiset(Seq[1..]);
    assert multiset(Seq) == multiset(Seq[0..1]) + multiset(Seq[1..]);
    assert multiset(Seq') == multiset(left) + multiset([pivot]) + multiset(right);
    assert multiset(Seq') == multiset([pivot]) + multiset(left) + multiset(right);
    assert multiset(Seq') == multiset([pivot]) + multiset(remaining);
    assert multiset(Seq') == multiset(Seq[0..1]) + multiset(Seq[1..]);
    assert multiset(Seq') == multiset(Seq);
  }
}