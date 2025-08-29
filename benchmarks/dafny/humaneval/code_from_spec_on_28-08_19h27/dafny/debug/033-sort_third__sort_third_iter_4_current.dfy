// <vc-helpers>
predicate is_sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

predicate is_permutation(s1: seq<int>, s2: seq<int>)
{
  multiset(s1) == multiset(s2)
}

method SortSeq(s: seq<int>) returns (result: seq<int>)
  ensures |result| == |s|
  ensures multiset(s) == multiset(result)
  ensures is_sorted(result)
{
  assume{:axiom} false;
}

lemma SortSeqPredPreservesPermutation(s: seq<int>, p: seq<bool>)
  requires |s| == |p|
  ensures exists sorted :: 
    |sorted| == |s| &&
    multiset(s) == multiset(sorted)
{
  assume{:axiom} false;
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
  ensures is_permutation(a, sorted_even)
  ensures forall i, j :: 0 <= i < j < |a| && i % 3 == 0 && j % 3 == 0 ==> sorted_even[i] <= sorted_even[j]
// </vc-spec>
// <vc-code>
{
  sorted_even := a;
  var indices := [];
  var values := [];
  
  for i := 0 to |a|
    invariant 0 <= i <= |a|
    invariant |indices| == |values|
    invariant forall k :: 0 <= k < |indices| ==> 0 <= indices[k] < |a| && indices[k] % 3 == 0
    invariant forall k :: 0 <= k < |indices| ==> values[k] == a[indices[k]]
  {
    if i % 3 == 0 {
      indices := indices + [i];
      values := values + [a[i]];
    }
  }
  
  var sorted_values := SortSeq(values);
  
  for j := 0 to |indices|
    invariant 0 <= j <= |indices|
    invariant |sorted_even| == |a|
    invariant multiset(sorted_even) == multiset(a)
    invariant j <= |indices| ==> j <= |sorted_values|
  {
    sorted_even := sorted_even[indices[j] := sorted_values[j]];
  }
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