method sorted_even(a: seq<int>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |a|
  ensures forall i, j :: 0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted| ==>
      sorted[2 * i] <= sorted[2 * j]
      ensures forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
      ensures multiset(a) == multiset(sorted)
  // post-conditions-end
{
  // impl-start
  var p := [];
  var i := 0;
  while i < |a|
    // invariants-start
    invariant 0 <= i <= |a|
    invariant |p| == i
    invariant forall j :: 0 <= j < i ==> p[j] == (j % 2 == 0)
    // invariants-end
  {
    p := p + [i % 2 == 0];
    i := i + 1;
  }

  sorted := SortSeqPred(a, p);
  // impl-end
}

method SortSeqPred(s: seq<int>, p: seq<bool>) returns (sorted: seq<int>)
  // pre-conditions-start
  requires |s| == |p|
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted| == |s|
  ensures forall i, j :: 0 <= i < j < |sorted| && p[i] && p[j] ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| && !p[i] ==> sorted[i] == s[i]
  // post-conditions-end
{
  // impl-start
  sorted := s;
  var i := 0;
  while i < |sorted|
    // invariants-start
    invariant 0 <= i <= |sorted|
    invariant |sorted| == |s|
    invariant forall j, k :: 0 <= j < k < i && p[j] && p[k] ==> sorted[j] <= sorted[k]
    invariant multiset(s) == multiset(sorted)
    invariant forall j :: 0 <= j < i && p[j] ==> forall k :: i <= k < |sorted| && p[k] ==> sorted[j] <= sorted[k]
    invariant |sorted| == |s|
    invariant forall j :: 0 <= j < |s| && !p[j] ==> sorted[j] == s[j]
    // invariants-end
  {
    if p[i] {
      var minIndex := i;
      var j := i + 1;
      while j < |sorted|
        // invariants-start
        invariant i <= minIndex < j <= |sorted|
        invariant p[minIndex]
        invariant forall k :: i <= k < j && p[k] ==> sorted[minIndex] <= sorted[k]
        // invariants-end
      {
        if p[j] && sorted[j] < sorted[minIndex] {
          minIndex := j;
        }
        j := j + 1;
      }
      if minIndex != i {
        var temp := sorted[i];
        sorted := sorted[i := sorted[minIndex]][minIndex := temp];
      }
    }
    i := i + 1;
  }
  // impl-end
}
