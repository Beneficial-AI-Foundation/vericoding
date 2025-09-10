method sort_third(a: seq<int>) returns (sorted_even: seq<int>)
  // pre-conditions-start
  requires |a| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures |sorted_even| == |a|
  ensures forall i, j :: 0 <= i < j < |sorted_even| && i % 3 == 0 && j % 3 == 0 ==>
      sorted_even[i] <= sorted_even[j]
  ensures forall i :: 0 <= i < |a| && i % 3 != 0 ==> sorted_even[i] == a[i]
  ensures multiset(a) == multiset(sorted_even)
  // post-conditions-end
{
  // impl-start
  var p := [];
  for i := 0 to |a|
    // invariants-start
    invariant |p| == i
    invariant forall j :: 0 <= j < i ==> p[j] == (j % 3 == 0)
    // invariants-end
  {
    p := p + [i % 3 == 0];
  }

  sorted_even := SortSeqPred(a, p);
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
  for i := 0 to |sorted|
    // invariants-start
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
      for j := i + 1 to |sorted|
        // invariants-start
        invariant i <= minIndex < j <= |sorted|
        invariant p[minIndex]
        invariant forall k :: i <= k < j && p[k] ==> sorted[minIndex] <= sorted[k]
        // invariants-end
      {
        if p[j] && sorted[j] < sorted[minIndex] {
          minIndex := j;
        }
      }
      if minIndex != i {
        var temp := sorted[i];
        sorted := sorted[i := sorted[minIndex]][minIndex := temp];
      }
    }
  }
  // impl-end
}
