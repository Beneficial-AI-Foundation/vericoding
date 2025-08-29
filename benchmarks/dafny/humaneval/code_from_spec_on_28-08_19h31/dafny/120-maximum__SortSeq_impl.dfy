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
function Multiset(s: seq<int>): multiset<int>
{
  if |s| == 0 then multiset{} else multiset{s[0]} + Multiset(s[1..])
}

lemma MultisetPreservesElements(s: seq<int>, sorted: seq<int>)
  requires Multiset(s) == Multiset(sorted)
  ensures forall x :: x in s ==> x in sorted
  ensures forall x :: x in sorted ==> x in s
{
}

lemma SortedSeqProperties(s: seq<int>, sorted: seq<int>)
  requires Multiset(s) == Multiset(sorted)
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && s[i] == sorted[j]
  ensures forall i :: 0 <= i < |sorted| ==> exists j :: 0 <= j < |s| && sorted[i] == s[j]
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
  var sortedSeq := SortSeq(s);
  var resultSeq := sortedSeq[|sortedSeq| - k..];
  return resultSeq;
}
// </vc-code>
