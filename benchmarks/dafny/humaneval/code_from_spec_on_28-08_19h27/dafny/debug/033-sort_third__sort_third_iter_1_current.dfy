// <vc-helpers>
predicate is_sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate is_permutation(s1: seq<int>, s2: seq<int>)
{
  multiset(s1) == multiset(s2)
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method sort_third(a: seq<int>) returns (sorted_even: seq<int>)
Sort elements. Requires: requires size of asize of  > 0. Ensures: returns the correct size/count; the result is sorted according to the ordering relation; the result is sorted according to the ordering relation; returns a sorted permutation of the input.
*/
// </vc-description>

// <vc-spec>
method sort_third(a: seq<int>) returns (sorted_even: seq<int>)
  requires |a| > 0
  ensures |sorted_even| == |a|
  ensures is_sorted(sorted_even)
  ensures is_permutation(a, sorted_even)
// </vc-spec>
// <vc-code>
{
  var pred := seq(|a|, i => i % 3 == 0);
  sorted_even := SortSeqPred(a, pred);
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