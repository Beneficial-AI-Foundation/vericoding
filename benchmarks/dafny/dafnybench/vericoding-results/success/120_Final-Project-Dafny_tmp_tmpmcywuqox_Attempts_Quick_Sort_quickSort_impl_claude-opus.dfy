predicate quickSorted(Seq: seq<int>)
{
  forall idx_1, idx_2 :: 0 <= idx_1 < idx_2 < |Seq| ==> Seq[idx_1] <= Seq[idx_2]
}

method threshold(thres:int,Seq:seq<int>) returns (Seq_1:seq<int>,Seq_2:seq<int>)
  ensures (forall x | x in Seq_1 :: x <= thres) && (forall x | x in Seq_2 :: x >= thres)
  ensures |Seq_1| + |Seq_2| == |Seq| 
  ensures multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma multisetDistribution(s1: seq<int>, s2: seq<int>, s3: seq<int>, s4: seq<int>)
  requires multiset(s1) + multiset(s2) == multiset(s3) + multiset(s4)
  ensures multiset(s1 + s2) == multiset(s3 + s4)
{
  assert multiset(s1 + s2) == multiset(s1) + multiset(s2);
  assert multiset(s3 + s4) == multiset(s3) + multiset(s4);
}

lemma multisetSplit(s: seq<int>)
  requires |s| >= 1
  ensures multiset(s) == multiset([s[0]]) + multiset(s[1..])
{
  assert s == [s[0]] + s[1..];
}
// </vc-helpers>

// <vc-spec>
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
    
    // Prove multiset preservation
    multisetSplit(Seq);
    assert multiset(Seq) == multiset([pivot]) + multiset(Seq[1..]);
    assert multiset(left) + multiset(right) == multiset(Seq[1..]);
    assert multiset(sortedLeft) == multiset(left);
    assert multiset(sortedRight) == multiset(right);
    multisetDistribution(sortedLeft, sortedRight, left, right);
    assert multiset(sortedLeft + sortedRight) == multiset(left + right);
    assert multiset([pivot]) + multiset(sortedLeft + sortedRight) == multiset([pivot]) + multiset(left + right);
    assert multiset(sortedLeft + [pivot] + sortedRight) == multiset([pivot]) + multiset(sortedLeft) + multiset(sortedRight);
    assert multiset(Seq') == multiset(Seq);
  }
}
// </vc-code>

