// <vc-helpers>
// Helper lemma to ensure properties of sorted and reversed sequences
lemma SortedReverseProperty(arr: seq<int>, sorted: seq<int>, rev: seq<int>)
  requires forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  requires |sorted| == |arr|
  requires multiset(arr) == multiset(sorted)
  requires |rev| == |sorted|
  requires forall k :: 0 <= k < |sorted| ==> rev[k] == sorted[|sorted| - 1 - k]
  ensures forall i, j :: 0 <= i < j < |rev| ==> rev[i] >= rev[j]
{
}

// Helper lemma to ensure string comparison based on numerical values
lemma StringMappingPreservesOrder(nums: seq<int>, strs: seq<string>)
  requires forall k :: 0 <= k < |nums| ==> 1 <= nums[k] <= 9
  requires |strs| == |nums|
  requires forall k :: 0 <= k < |nums| ==> strs[k] == NumberToName(nums[k])
  requires forall i, j :: 0 <= i < j < |nums| ==> nums[i] >= nums[j]
  ensures forall i, j :: 0 <= i < j < |strs| ==> CompareStrings(strs[i], strs[j]) >= 0
{
}

// Function to define string comparison for ensuring reverse order
function CompareStrings(s1: string, s2: string): int
{
  if s1 < s2 then -1 else if s1 == s2 then 0 else 1
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method SortReverseAndName(arr: seq<int>) returns (result: seq<string>)
Sort elements. Ensures: the size is bounded; the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method SortReverseAndName(arr: seq<int>) returns (result: seq<string>)
  requires forall x :: x in arr ==> 1 <= x <= 9
  ensures |result| == |arr|
  ensures forall i, j :: 0 <= i < j < |result| ==> CompareStrings(result[i], result[j]) >= 0
// </vc-spec>
// <vc-code>
{
  var sorted := SortSeq(arr);
  assert forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j];
  var reversed := reverse(sorted);
  SortedReverseProperty(arr, sorted, reversed);
  assert forall i, j :: 0 <= i < j < |reversed| ==> reversed[i] >= reversed[j];
  var resultSeq: seq<string> := [];
  var i := 0;
  while i < |reversed|
    invariant 0 <= i <= |reversed|
    invariant |resultSeq| == i
    invariant forall k :: 0 <= k < i ==> resultSeq[k] == NumberToName(reversed[k])
    invariant forall k :: 0 <= k < i ==> 1 <= reversed[k] <= 9
  {
    resultSeq := resultSeq + [NumberToName(reversed[i])];
    i := i + 1;
  }
  StringMappingPreservesOrder(reversed, resultSeq);
  return resultSeq;
}
// </vc-code>

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}
method reverse(s: seq<int>) returns (rev: seq<int>)
  // post-conditions-start
  ensures |rev| == |s|
  ensures forall k :: 0 <= k < |s| ==> rev[k] == s[|s| - 1 - k]
  // post-conditions-end
{
  assume{:axiom} false;
}
function NumberToName(n: int): string
  requires 1 <= n <= 9
{
  match n
  case 1 => "One"
  case 2 => "Two"
  case 3 => "Three"
  case 4 => "Four"
  case 5 => "Five"
  case 6 => "Six"
  case 7 => "Seven"
  case 8 => "Eight"
  case 9 => "Nine"
}
// pure-end