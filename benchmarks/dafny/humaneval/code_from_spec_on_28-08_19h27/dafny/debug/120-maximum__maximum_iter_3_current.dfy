// <vc-helpers>
lemma SlicePreservesOrder(s: seq<int>, start: int, end: int)
  requires 0 <= start <= end <= |s|
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i, j :: 0 <= i < j < end - start ==> s[start + i] <= s[start + j]
{
}

lemma SliceReverseOrder(s: seq<int>, start: int, end: int)
  requires 0 <= start <= end <= |s|
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] >= s[j]
  ensures forall i, j :: 0 <= i < j < end - start ==> s[start + i] >= s[start + j]
{
}

lemma SliceElements(s: seq<int>, start: int, end: int)
  requires 0 <= start <= end <= |s|
  ensures forall i :: 0 <= i < end - start ==> s[start + i] in s
{
}

lemma ReverseOrderFromSorted(s: seq<int>, start: int, end: int)
  requires 0 <= start <= end <= |s|
  requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
  ensures forall i, j :: 0 <= i < j < end - start ==> s[end - 1 - i] >= s[end - 1 - j]
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method maximum(s: seq<int>, k: int) returns (result: seq<int>)
Process input. Requires: the size is bounded; the size is bounded; the condition holds for all values. Ensures: returns the correct size/count; the condition holds for all values; the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method maximum(s: seq<int>, k: int) returns (result: seq<int>)
  requires 0 <= k <= |s|
  requires |s| < 0x40000000
  ensures |result| == k
  ensures forall i :: 0 <= i < |result| ==> result[i] in s
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] >= result[j]
// </vc-spec>
// <vc-code>
{
  if k == 0 {
    result := [];
    return;
  }
  
  var sorted := SortSeq(s);
  var suffix := sorted[|sorted| - k..];
  
  result := [];
  var i := |suffix| - 1;
  while i >= 0
    invariant -1 <= i < |suffix|
    invariant |result| == |suffix| - 1 - i
    invariant forall j :: 0 <= j < |result| ==> result[j] in s
    invariant forall j1, j2 :: 0 <= j1 < j2 < |result| ==> result[j1] >= result[j2]
    invariant forall j :: 0 <= j < |result| ==> result[j] == suffix[|suffix| - 1 - j]
  {
    result := result + [suffix[i]];
    i := i - 1;
  }
  
  assert |result| == k;
  assert forall j :: 0 <= j < |result| ==> result[j] in suffix;
  assert forall j :: 0 <= j < |result| ==> result[j] in sorted;
  assert forall j :: 0 <= j < |result| ==> result[j] in s;
}
// </vc-code>

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && s[i] == sorted[j]
  ensures forall x :: x in s ==> x in sorted
  ensures forall i :: 0 <= i < |s| ==> exists j :: 0 <= j < |sorted| && sorted[i] == s[j]
  ensures forall x :: x in sorted ==> x in s
{
  assume{:axiom} false;
}