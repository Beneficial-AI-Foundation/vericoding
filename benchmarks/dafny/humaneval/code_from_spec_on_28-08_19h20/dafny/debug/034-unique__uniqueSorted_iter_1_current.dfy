// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: method uniqueSorted(s: seq<int>) returns (result: seq<int>)
Sort elements. Requires: the condition holds for all values. Ensures: the condition holds for all values; the condition holds for all values; the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
// </vc-spec>
// <vc-code>
method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
{
    var uniqueSeq := unique(s);
    result := uniqueSeq;
}
// </vc-code>

method unique(s: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
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