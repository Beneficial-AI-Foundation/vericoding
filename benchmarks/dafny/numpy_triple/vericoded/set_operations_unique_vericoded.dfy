// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}

predicate hasNoDuplicates(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

/* helper modified by LLM (iteration 2): strengthened postcondition to maintain elements from input */
method insertSorted(s: seq<int>, x: int) returns (r: seq<int>)
  requires sorted(s)
  requires hasNoDuplicates(s)
  requires x !in s
  ensures sorted(r)
  ensures hasNoDuplicates(r)
  ensures |r| == |s| + 1
  ensures x in r
  ensures forall y :: y in s ==> y in r
  ensures forall y :: y in r ==> y == x || y in s
{
  if |s| == 0 {
    r := [x];
  } else if x < s[0] {
    r := [x] + s;
  } else if x > s[|s| - 1] {
    r := s + [x];
  } else {
    var i := 0;
    while i < |s| && s[i] < x
      invariant 0 <= i <= |s|
      invariant forall j :: 0 <= j < i ==> s[j] < x
    {
      i := i + 1;
    }
    r := s[..i] + [x] + s[i..];
  }
}
// </vc-helpers>

// <vc-spec>
method unique(arr: seq<int>) returns (result: seq<int>)
    ensures |result| <= |arr|
    // Result is sorted in ascending order
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    // Every element in result exists in the input array
    ensures forall i :: 0 <= i < |result| ==> result[i] in arr
    // All elements in result are unique (no duplicates)
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
    // Every element in input array appears in the result
    ensures forall x :: x in arr ==> x in result
    // Equivalently: every index in input has its value represented in result
    ensures forall i :: 0 <= i < |arr| ==> arr[i] in result
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): strengthened loop invariant to track all elements in seen come from arr */
  var seen := [];
  var i := 0;
  
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant sorted(seen)
    invariant hasNoDuplicates(seen)
    invariant forall x :: x in seen ==> x in arr
    invariant forall j :: 0 <= j < i ==> arr[j] in seen
    invariant |seen| <= i
  {
    if arr[i] !in seen {
      seen := insertSorted(seen, arr[i]);
    }
    i := i + 1;
  }
  
  result := seen;
}
// </vc-code>
