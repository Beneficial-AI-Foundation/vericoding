predicate quickSorted(Seq: seq<int>)
{
  forall idx_1, idx_2 :: 0 <= idx_1 < idx_2 < |Seq| ==> Seq[idx_1] <= Seq[idx_2]
}

// <vc-helpers>
lemma MultisetSliceNext(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures multiset(s[..i+1]) == multiset(s[..i]) + multiset{s[i]}
{
  assert s[..i+1] == s[..i] + [s[i]];
}
// </vc-helpers>

// <vc-spec>
method threshold(thres:int,Seq:seq<int>) returns (Seq_1:seq<int>,Seq_2:seq<int>)
  ensures (forall x | x in Seq_1 :: x <= thres) && (forall x | x in Seq_2 :: x >= thres)
  ensures |Seq_1| + |Seq_2| == |Seq| 
  ensures multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
// </vc-spec>
// <vc-code>
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
      MultisetSliceNext(Seq, i);
      Seq_1 := Seq_1 + [Seq[i]];
    } else {
      MultisetSliceNext(Seq, i);
      Seq_2 := Seq_2 + [Seq[i]];
    }
    i := i + 1;
  }
  
  assert Seq[..|Seq|] == Seq;
}
// </vc-code>

