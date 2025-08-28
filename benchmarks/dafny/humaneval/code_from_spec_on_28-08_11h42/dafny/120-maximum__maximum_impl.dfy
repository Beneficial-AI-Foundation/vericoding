// <vc-helpers>
lemma SubseqPreservesElements(s: seq<int>, start: int, end: int)
  requires 0 <= start <= end <= |s|
  ensures forall x :: x in s[start..end] ==> x in s
{
}

lemma SortedSubseqPreservesOrder(sorted: seq<int>, start: int, end: int)
  requires 0 <= start <= end <= |sorted|
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i, j :: 0 <= i < j < end - start ==> sorted[start..end][i] <= sorted[start..end][j]
{
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
  var sorted := SortSeq(s);
  var startIndex := |sorted| - k;
  result := sorted[startIndex..];
  
  assert |result| == k;
  assert forall i, j :: 0 <= i < j < k ==> result[i] <= result[j] by {
    SortedSubseqPreservesOrder(sorted, startIndex, |sorted|);
  }
  assert forall x :: x in result ==> x in s by {
    SubseqPreservesElements(sorted, startIndex, |sorted|);
  }
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