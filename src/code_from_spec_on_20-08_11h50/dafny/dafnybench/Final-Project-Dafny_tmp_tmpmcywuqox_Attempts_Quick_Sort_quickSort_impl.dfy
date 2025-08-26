predicate quickSorted(Seq: seq<int>)
{
  forall idx_1, idx_2 :: 0 <= idx_1 < idx_2 < |Seq| ==> Seq[idx_1] <= Seq[idx_2]
}

// <vc-spec>
method threshold(thres:int,Seq:seq<int>) returns (Seq_1:seq<int>,Seq_2:seq<int>)
  ensures (forall x | x in Seq_1 :: x <= thres) && (forall x | x in Seq_2 :: x >= thres)
  ensures |Seq_1| + |Seq_2| == |Seq| 
  ensures multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
{
  Seq_1 := [];
  Seq_2 := [];
  var i := 0;
  while (i < |Seq|)
    invariant i <= |Seq|
    invariant (forall x | x in Seq_1 :: x <= thres) && (forall x | x in Seq_2 :: x >= thres)
    invariant |Seq_1| + |Seq_2| == i
    invariant multiset(Seq[..i]) == multiset(Seq_1) + multiset(Seq_2)
  {
    if (Seq[i] <= thres) {
      Seq_1 := Seq_1 + [Seq[i]];
    } else {
      Seq_2 := Seq_2 + [Seq[i]];
    }
    assert (Seq[..i] + [Seq[i]]) == Seq[..i+1];  
    i := i + 1;
  }
  assert (Seq[..|Seq|] == Seq);  
}


lemma Lemma_1(Seq_1:seq,Seq_2:seq)  // The proof of the lemma is not necessary
  requires multiset(Seq_1) == multiset(Seq_2)
  ensures forall x | x in Seq_1 :: x in Seq_2

{
  forall x | x in Seq_1
    ensures x in multiset(Seq_1)
  {
    var i := 0;
    while (i < |Seq_1|)
      invariant 0 <= i <= |Seq_1|
      invariant forall idx_1 | 0 <= idx_1 < i :: Seq_1[idx_1] in multiset(Seq_1)
    {
      i := i + 1;
    }
  }

}

// <vc-helpers>
lemma multisetConcat<T>(s1: seq<T>, s2: seq<T>, s3: seq<T>)
  ensures multiset(s1 + s2 + s3) == multiset(s1) + multiset(s2) + multiset(s3)
{
}

lemma seqDecomposition<T>(s: seq<T>)
  requires |s| > 0
  ensures multiset([s[0]]) + multiset(s[1..]) == multiset(s)
{
  assert s == [s[0]] + s[1..];
}
// </vc-helpers>

method quickSort(Seq: seq<int>) returns (Seq': seq<int>)
  ensures multiset(Seq) == multiset(Seq')
  decreases |Seq|
// </vc-spec>
// <vc-code>
{
  if |Seq| <= 1 {
    Seq' := Seq;
  } else {
    var pivot := Seq[0];
    var left, right := threshold(pivot, Seq[1..]);
    var sortedLeft := quickSort(left);
    var sortedRight := quickSort(right);
    Seq' := sortedLeft + [pivot] + sortedRight;
    
    // Proof that multisets are preserved
    assert multiset(left) + multiset(right) == multiset(Seq[1..]);
    assert multiset(sortedLeft) == multiset(left);
    assert multiset(sortedRight) == multiset(right);
    multisetConcat(sortedLeft, [pivot], sortedRight);
    assert multiset(Seq') == multiset(sortedLeft) + multiset([pivot]) + multiset(sortedRight);
    assert multiset(Seq') == multiset(left) + multiset([pivot]) + multiset(right);
    seqDecomposition(Seq);
    assert multiset([pivot]) + multiset(Seq[1..]) == multiset(Seq);
    assert multiset(Seq') == multiset(Seq);
  }
}
// </vc-code>