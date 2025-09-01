

// <vc-helpers>
predicate sorted_by_predicate(s: seq<int>, p: seq<bool>)
  requires |s| == |p|
{
  forall i, j :: 0 <= i < j < |s| && p[i] && p[j] ==> s[i] <= s[j]
}

// NOTE: Moved the SortSeqPred method from here.
// It was causing a "Duplicate member name" error because it was defined twice.
// The actual implementation is provided after the vc-code block in the original problem structure.
// This block should only contain helpers not already defined in the problem description outside of this block.
// </vc-helpers>

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
  var p: seq<bool> := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |p| == i
    decreases |a| - i
  {
    p := p + [(i % 2 == 0)];
    i := i + 1;
  }

  var sorted_result := SortSeqPred(a, p);

  return sorted_result;
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