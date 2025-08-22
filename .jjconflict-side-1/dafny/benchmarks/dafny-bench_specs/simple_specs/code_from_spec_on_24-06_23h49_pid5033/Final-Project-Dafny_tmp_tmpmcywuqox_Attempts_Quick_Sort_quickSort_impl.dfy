//ATOM threshold
method threshold(thres:int,Seq:seq<int>) returns (Seq_1:seq<int>,Seq_2:seq<int>)
 ensures (forall x | x in Seq_1 :: x <= thres) && (forall x | x in Seq_2 :: x >= thres)
 ensures |Seq_1| + |Seq_2| == |Seq| 
 ensures multiset(Seq_1) + multiset(Seq_2) == multiset(Seq)
{
  Seq_1 := [];
  Seq_2 := [];
  assume (forall x | x in Seq_1 :: x <= thres) && (forall x | x in Seq_2 :: x >= thres);
  assume |Seq_1| + |Seq_2| == |Seq|;
  assume multiset(Seq_1) + multiset(Seq_2) == multiset(Seq);
  return Seq_1, Seq_2;
}

//IMPL quickSort
method quickSort(Seq: seq<int>) returns (Seq': seq<int>)
 ensures multiset(Seq) == multiset(Seq')
 decreases |Seq|
{
  if |Seq| <= 1 {
    return Seq;
  }
  
  var pivot := Seq[0];
  var left, right := threshold(pivot, Seq);
  
  /* code modified by LLM (iteration 2): fix degenerate case handling */
  if |left| == |Seq| {
    // All elements are <= pivot, remove one occurrence of pivot from left
    var pivotRemoved := false;
    var newLeft: seq<int> := [];
    var i := 0;
    while i < |left|
      invariant 0 <= i <= |left|
      invariant |newLeft| <= i
    {
      if left[i] == pivot && !pivotRemoved {
        pivotRemoved := true;
      } else {
        newLeft := newLeft + [left[i]];
      }
      i := i + 1;
    }
    
    if |newLeft| == 0 {
      Seq' := [pivot];
      return;
    }
    
    var sortedLeft := quickSort(newLeft);
    Seq' := sortedLeft + [pivot];
    return;
  }
  
  if |right| == |Seq| {
    // All elements are >= pivot, remove one occurrence of pivot from right  
    var pivotRemoved := false;
    var newRight: seq<int> := [];
    var i := 0;
    while i < |right|
      invariant 0 <= i <= |right|
      invariant |newRight| <= i
    {
      if right[i] == pivot && !pivotRemoved {
        pivotRemoved := true;
      } else {
        newRight := newRight + [right[i]];
      }
      i := i + 1;
    }
    
    if |newRight| == 0 {
      Seq' := [pivot];
      return;
    }
    
    var sortedRight := quickSort(newRight);
    Seq' := [pivot] + sortedRight;
    return;
  }
  
  /* code modified by LLM (iteration 2): normal case - remove pivot from one partition */
  // Remove pivot from left partition to ensure progress
  var pivotRemoved := false;
  var newLeft: seq<int> := [];
  var i := 0;
  while i < |left|
    invariant 0 <= i <= |left|
    invariant |newLeft| <= i
  {
    if left[i] == pivot && !pivotRemoved {
      pivotRemoved := true;
    } else {
      newLeft := newLeft + [left[i]];
    }
    i := i + 1;
  }
  
  var sortedLeft := quickSort(newLeft);
  var sortedRight := quickSort(right);
  
  Seq' := sortedLeft + [pivot] + sortedRight;
}