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
lemma PartitionPreservesMultiset(Seq: seq<int>, Seq_1: seq<int>, Seq_2: seq<int>, thres: int)
  requires |Seq_1| + |Seq_2| == |Seq|
  requires multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
  ensures multiset(Seq) == multiset(Seq_1) + multiset(Seq_2)
{
}

lemma ThresholdLength(Seq: seq<int>, Seq_1: seq<int>, Seq_2: seq<int>, thres: int)
  requires |Seq_1| + |Seq_2| == |Seq|
  requires forall x | x in Seq_1 :: x <= thres
  requires forall x | x in Seq_2 :: x >= thres
  ensures |Seq_1| < |Seq| || |Seq_2| < |Seq|
{
  if |Seq| == 0 {
    assert |Seq_1| == 0 && |Seq_2| == 0;
  } else if |Seq_1| == 0 {
    assert |Seq_2| == |Seq|;
    assert |Seq_1| < |Seq|;
  } else if |Seq_2| == 0 {
    assert |Seq_1| == |Seq|;
    assert |Seq_2| < |Seq|;
  } else {
    assert |Seq_1| >= 1 && |Seq_2| >= 1;
    assert |Seq_1| + |Seq_2| == |Seq|;
    assert |Seq_1| < |Seq| && |Seq_2| < |Seq| by {
      calc {
        |Seq_1| + |Seq_2|;
        == |Seq|;
      }
      assert |Seq_1| <= |Seq| - 1;
      assert |Seq_2| <= |Seq| - 1;
    }
  }
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
  
  var pivot := Seq[|Seq| / 2];
  var left, right := threshold(pivot, Seq);
  
  assert |left| < |Seq| || |right| < |Seq| by {
    ThresholdLength(Seq, left, right, pivot);
  }
  
  var leftSorted := quickSort(left);
  var rightSorted := quickSort(right);
  
  Seq' := leftSorted + rightSorted;
}
// </vc-code>
