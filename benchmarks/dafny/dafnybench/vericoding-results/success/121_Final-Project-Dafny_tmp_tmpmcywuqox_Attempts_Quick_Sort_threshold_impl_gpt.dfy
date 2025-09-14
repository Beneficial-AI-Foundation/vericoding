predicate quickSorted(Seq: seq<int>)
{
  forall idx_1, idx_2 :: 0 <= idx_1 < idx_2 < |Seq| ==> Seq[idx_1] <= Seq[idx_2]
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method threshold(thres:int,Seq:seq<int>) returns (Seq_1:seq<int>,Seq_2:seq<int>)
  ensures (forall x | x in Seq_1 :: x <= thres) && (forall x | x in Seq_2 :: x >= thres)
  ensures |Seq_1| + |Seq_2| == |Seq| 
  ensures multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  Seq_1 := [];
  Seq_2 := [];
  while i < |Seq|
    invariant 0 <= i <= |Seq|
    invariant |Seq_1| + |Seq_2| == i
    invariant (forall x | x in Seq_1 :: x <= thres)
    invariant (forall x | x in Seq_2 :: x >= thres)
    invariant multiset(Seq_1) + multiset(Seq_2) == multiset(Seq[..i])
    decreases |Seq| - i
  {
    if Seq[i] <= thres {
      Seq_1 := Seq_1 + [Seq[i]];
    } else {
      Seq_2 := Seq_2 + [Seq[i]];
    }
    assert Seq[..i] + [Seq[i]] == Seq[..i+1];
    i := i + 1;
  }
  assert i == |Seq|;
  assert Seq[..i] == Seq;
}
// </vc-code>

