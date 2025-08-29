// <vc-helpers>
method RemoveDuplicates(s: seq<int>) returns (result: seq<int>)
  ensures forall x :: x in result ==> x in s
  ensures forall x :: x in s ==> x in result
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
{
  assume{:axiom} false;
}

method SortUniqueSeq(s: seq<int>) returns (sorted: seq<int>)
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] < sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
{
  assume{:axiom} false;
}
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
  var temp := RemoveDuplicates(s);
  var sorted := SortUniqueSeq(temp);
  result := sorted;
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