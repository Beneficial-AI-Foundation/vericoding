// <vc-helpers>
// Helper predicate to check if a sequence is sorted
predicate IsSorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method sort_array(s: seq<int>) returns (sorted: seq<int>)
Sort elements. Ensures: returns the correct size/count; returns the correct size/count; returns the correct size/count.
*/
// </vc-description>

// <vc-spec>
method sort_array(s: seq<int>) returns (sorted: seq<int>)
  requires true
  ensures |sorted| == |s|
  ensures IsSorted(sorted)
  ensures multiset(s) == multiset(sorted)
// </vc-spec>
// <vc-code>
{
  sorted := SortSeq(s);
}
// </vc-code>

method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // post-conditions-end
{
  assume{:axiom} false;
}
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}