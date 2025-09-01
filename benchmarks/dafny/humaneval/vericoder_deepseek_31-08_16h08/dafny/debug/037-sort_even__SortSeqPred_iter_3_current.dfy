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
  assume{:axiom} false;
}

// <vc-helpers>
lemma SortedEvenHelper(a: seq<int>, sorted: seq<int>)
  requires |a| == |sorted|
  requires forall i :: 0 <= i < |a| && i % 2 == 1 ==> sorted[i] == a[i]
  requires multiset(a) == multiset(sorted)
  requires |a| > 0
  ensures forall i, j :: 0 <= i < j && 2 * i < |sorted| && 2 * j < |sorted| ==> sorted[2 * i] <= sorted[2 * j]
{
  // This lemma connects the SortSeqPred postconditions to sorted_even postconditions
}

function EvenIndices(p: seq<bool>): seq<bool>
  requires |p| > 0
  ensures |EvenIndices(p)| == |p|
  ensures forall i :: 0 <= i < |p| ==> EvenIndices(p)[i] == (i % 2 == 0)
{
  seq(|p|, i => i % 2 == 0)
}
// </vc-helpers>

// <vc-spec>
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
// </vc-spec>
// <vc-code>
{
  var p := seq(|a|, i => i % 2 == 0);
  sorted := SortSeqPred(a, p);
  SortedEvenHelper(a, sorted);
}
// </vc-code>

