

// <vc-helpers>
method SortSeqHelper(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
{
  if |s| == 0 {
    return [];
  }
  
  sorted := [s[0]];
  var i := 1;
  while i < |s|
    invariant 1 <= i <= |s|
    invariant |sorted| == i
    invariant forall j,k :: 0 <= j < k < |sorted| ==> sorted[j] <= sorted[k]
    invariant multiset(s[0..i]) == multiset(sorted)
  {
    var key := s[i];
    var pos := 0;
    while pos < |sorted| && sorted[pos] <= key
      invariant 0 <= pos <= |sorted|
      invariant forall j :: 0 <= j < pos ==> sorted[j] <= key
    {
      pos := pos + 1;
    }
    sorted := sorted[0..pos] + [key] + sorted[pos..];
    i := i + 1;
  }
  return sorted;
}
// </vc-helpers>

// <vc-spec>
method maximum(s: seq<int>, k: int) returns (result: seq<int>)
  // pre-conditions-start
  requires 1 <= k <= |s|
  requires 1 <= |s| <= 1000
  requires forall x :: x in s ==> -1000 <= x <= 1000
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == k
  ensures forall i, j :: 0 <= i < j < k ==> result[i] <= result[j]
  ensures forall x :: x in result ==> x in s
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var sortedSeq := SortSeqHelper(s);
  assert 0 <= |s| - k <= |s|;
  result := sortedSeq[|s| - k .. |s|];
}
// </vc-code>

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && s[i] == sorted[j]
  ensures forall x :: x in s ==> x in sorted
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && sorted[i] == s[j]
  ensures forall x :: x in sorted ==> x in s
{
  assume{:axiom} false;
}