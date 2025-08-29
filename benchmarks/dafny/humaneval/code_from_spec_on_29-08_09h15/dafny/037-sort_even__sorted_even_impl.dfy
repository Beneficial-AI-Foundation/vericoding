

// <vc-helpers>
predicate IsEven(i: int) { i % 2 == 0 }

lemma MultisetPreservation(a: seq<int>, sorted: seq<int>)
  requires |a| == |sorted|
  requires multiset(a) == multiset(sorted)
  ensures forall x :: x in a <==> x in sorted

lemma EvenPositionsCount(s: seq<int>)
  ensures |s| > 0 ==> exists i :: 0 <= i < |s| && i % 2 == 0
// </vc-helpers>

// <vc-description>
/*
function_signature: method sorted_even(a: seq<int>) returns (sorted: seq<int>)
Sort elements. Requires: requires size of asize of  > 0. Ensures: returns the correct size/count; the result is sorted according to the ordering relation; the result is sorted according to the ordering relation; returns a sorted permutation of the input.
*/
// </vc-description>

// <vc-spec>
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
// </vc-spec>

// <vc-code>
{
  var predicate_seq := seq(|a|, i requires 0 <= i < |a| => i % 2 == 0);
  sorted := SortSeqPred(a, predicate_seq);
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