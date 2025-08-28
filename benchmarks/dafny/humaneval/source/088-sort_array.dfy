method sort_array(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures |sorted| == |s|
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 == 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] >= sorted[j]
  ensures |s| > 0 && (s[0] + s[|s| - 1]) % 2 != 0 ==>
    forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  // post-conditions-end
{
  // impl-start
  if |s| == 0 {
    sorted := [];
  } else if (s[0] + s[|s| - 1]) % 2 == 0 {
    var t := SortSeq(s);
    sorted := reverse(t);
    return;
  } else {
    sorted := SortSeq(s);
    return;
  }
  // impl-end
}

method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // post-conditions-end
{
  // impl-start
  rev := [];
  var i := 0;
  while (i < |s|)
    // invariants-start
    invariant i >= 0 && i <= |s|
    invariant |rev| == i
    invariant forall k :: 0 <= k < i ==> rev[k] == s[|s| - 1 - k]
    // invariants-end
  {
    rev := rev + [s[|s| - i - 1]];
    i := i + 1;
  }
  // impl-end
}


method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  // impl-start
  sorted := s;
  var i := 0;
  while i < |sorted|
    // invariants-start
    invariant 0 <= i <= |sorted|
    invariant forall j, k :: 0 <= j < k < i ==> sorted[j] <= sorted[k]
    invariant multiset(s) == multiset(sorted)
    invariant forall j :: 0 <= j < i ==> forall k :: i <= k < |sorted| ==> sorted[j] <= sorted[k]
    invariant |sorted| == |s|
    // invariants-end
  {
    var minIndex := i;
    var j := i + 1;
    while j < |sorted|
      // invariants-start
      invariant i <= minIndex < j <= |sorted|
      invariant forall k :: i <= k < j ==> sorted[minIndex] <= sorted[k]
      // invariants-end
    {
      if sorted[j] < sorted[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    if minIndex != i {
      var temp := sorted[i];
      sorted := sorted[i := sorted[minIndex]][minIndex := temp];
    }
    i := i + 1;
  }
  // impl-end
}
