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
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma SortedSeqProperties(s: seq<int>, sorted: seq<int>)
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  requires multiset(s) == multiset(sorted)
  ensures |sorted| == |s|
  ensures forall x :: x in s ==> x in sorted
  ensures forall x :: x in sorted ==> x in s
{
}

lemma MultisetContainsSameElements(s: seq<int>, t: seq<int>)
  requires multiset(s) == multiset(t)
  ensures forall x :: x in s ==> x in t
  ensures forall x :: x in t ==> x in s
{
}

lemma SortedSubsequenceProperties(sorted: seq<int>, k: int, result: seq<int>)
  requires 1 <= k <= |sorted|
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  requires result == sorted[|sorted|-k..]
  ensures |result| == k
  ensures forall i, j :: 0 <= i < j < k ==> result[i] <= result[j]
  ensures forall x :: x in result ==> x in sorted
{
}
// </vc-helpers>

// <vc-spec>
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && s[i] == sorted[j]
  ensures forall x :: x in s ==> x in sorted
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && sorted[i] == s[j]
  ensures forall x :: x in sorted ==> x in s
// </vc-spec>
// <vc-code>
{
  var sortedSeq := sort(s);
  var n := |sortedSeq|;
  result := sortedSeq[n-k..];
}
// </vc-code>

