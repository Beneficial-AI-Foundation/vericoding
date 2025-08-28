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
lemma multisetPreservation(s1: seq<int>, s2: seq<int>, pivot: int)
  requires |s1| + |s2| > 0
  requires multiset(s1) + multiset(s2) == multiset([pivot] + s1 + s2)
  ensures multiset([pivot] + s1 + s2) == multiset(s1 + [pivot] + s2)
{
}

lemma concatenationMultiset(s1: seq<int>, s2: seq<int>, s3: seq<int>)
  ensures multiset(s1 + s2 + s3) == multiset(s1) + multiset(s2) + multiset(s3)
{
}

lemma quickSortMultisetPreservation(Seq: seq<int>, left: seq<int>, right: seq<int>, pivot: int)
  requires |Seq| > 1
  requires pivot == Seq[0]
  requires multiset(left) + multiset(right) == multiset(Seq[1..])
  ensures multiset(Seq) == multiset(left) + multiset([pivot]) + multiset(right)
{
  assert Seq == [pivot] + Seq[1..];
  assert multiset(Seq) == multiset([pivot] + Seq[1..]);
  assert multiset([pivot] + Seq[1..]) == multiset([pivot]) + multiset(Seq[1..]);
  assert multiset(Seq[1..]) == multiset(left) + multiset(right);
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method quickSort(Seq: seq<int>) returns (Seq': seq<int>)
  ensures multiset(Seq) == multiset(Seq')
  decreases |Seq|
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  if |Seq| <= 1 {
    return Seq;
  }
  
  var pivot := Seq[0];
  var rest := Seq[1..];
  
  var left, right := threshold(pivot, rest);
  
  var sortedLeft := quickSort(left);
  var sortedRight := quickSort(right);
  
  Seq' := sortedLeft + [pivot] + sortedRight;
  
  concatenationMultiset(sortedLeft, [pivot], sortedRight);
  quickSortMultisetPreservation(Seq, left, right, pivot);
  
  assert multiset(Seq) == multiset(left) + multiset([pivot]) + multiset(right);
  assert multiset(sortedLeft) == multiset(left);
  assert multiset(sortedRight) == multiset(right);
  assert multiset(Seq') == multiset(sortedLeft) + multiset([pivot]) + multiset(sortedRight);
  assert multiset(Seq') == multiset(left) + multiset([pivot]) + multiset(right);
}
// </vc-code>
