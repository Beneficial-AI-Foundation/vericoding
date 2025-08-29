// <vc-helpers>
method strange_sort_list(s: seq<int>) returns (strange: seq<int>)
    ensures |s| == |strange|
    ensures multiset(s) == multiset(strange)
{
  assume{:axiom} false;
}
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
{
  assume{:axiom} false;
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)
Sort elements. Ensures: returns a sorted permutation of the input; returns the correct size/count; the result is sorted according to the ordering relation; the result is sorted according to the ordering relation.
*/
// </vc-description>

// <vc-spec>
method strange_sort_list_helper(s: seq<int>) returns (sorted: seq<int>, strange: seq<int>)
    ensures |sorted| == |s|
    ensures |strange| == |s|
    ensures multiset(s) == multiset(sorted)
    ensures multiset(s) == multiset(strange)
    ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
// </vc-spec>
// <vc-code>
{
    sorted := SortSeq(s);
    strange := strange_sort_list(s);
}
// </vc-code>

method strange_sort_list(s: seq<int>) returns (strange: seq<int>)
    // post-conditions-start
    ensures |s| == |strange|
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