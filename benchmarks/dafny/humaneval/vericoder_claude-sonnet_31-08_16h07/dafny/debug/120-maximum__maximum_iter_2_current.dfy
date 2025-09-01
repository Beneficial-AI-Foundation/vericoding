

// <vc-helpers>
lemma SortedSliceStillSorted(s: seq<int>, start: int, end: int)
  requires 0 <= start <= end <= |s|
  requires forall i, j {:trigger s[i], s[j]} :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i, j {:trigger s[start + i], s[start + j]} :: 0 <= i < j < (end - start) ==> s[start + i] <= s[start + j]
{
}

lemma SlicePreservesElements(s: seq<int>, start: int, end: int)
  requires 0 <= start <= end <= |s|
  ensures forall x :: x in s[start..end] ==> x in s
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
  var sliceStart := |sorted| - k;
  result := sorted[sliceStart..];
  
  SortedSliceStillSorted(sorted, sliceStart, |sorted|);
  SlicePreservesElements(sorted, sliceStart, |sorted|);
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