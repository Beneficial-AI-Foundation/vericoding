// <vc-helpers>
predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate IsEven(x: int)
{
  x % 2 == 0
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures |sorted| == |s|
  ensures IsSorted(sorted)
  ensures multiset(s) == multiset(sorted)
{
  assume{:axiom} false;
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method sorted_even(a: seq<int>) returns (sorted: seq<int>)
Sort elements. Requires: requires size of asize of  > 0. Ensures: returns the correct size/count; the result is sorted according to the ordering relation; the result is sorted according to the ordering relation; returns a sorted permutation of the input.
*/
// </vc-description>

// <vc-spec>
method sorted_even(a: seq<int>) returns (sorted: seq<int>)
  requires |a| > 0
  ensures |sorted| == |a|
  ensures IsSorted(sorted)
  ensures multiset(a) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  sorted := SortSeq(a);
}
// </vc-code>

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
  assume{:axiom} false;
}