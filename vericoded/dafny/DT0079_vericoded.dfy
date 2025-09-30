// <vc-preamble>
// Method that finds unique elements in an array and returns them sorted
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed isSubsetOf to check against full array instead of slice */
predicate isSorted(s: seq<real>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}

predicate hasNoDuplicates(s: seq<real>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

predicate isSubsetOf(s: seq<real>, arr: seq<real>)
{
  forall x :: x in s ==> x in arr
}

method insertSorted(s: seq<real>, x: real) returns (result: seq<real>)
  requires isSorted(s)
  requires hasNoDuplicates(s)
  requires x !in s
  ensures isSorted(result)
  ensures hasNoDuplicates(result)
  ensures |result| == |s| + 1
  ensures x in result
  ensures forall y :: y in s ==> y in result
  ensures forall y :: y in result ==> y == x || y in s
{
  var i := 0;
  while i < |s| && s[i] < x
    invariant 0 <= i <= |s|
    invariant forall j :: 0 <= j < i ==> s[j] < x
  {
    i := i + 1;
  }
  result := s[..i] + [x] + s[i..];
}
// </vc-helpers>

// <vc-spec>
method numpy_unique(arr: seq<real>) returns (unique_arr: seq<real>)
  ensures // The result is sorted in ascending order
          forall i, j :: 0 <= i < j < |unique_arr| ==> unique_arr[i] < unique_arr[j]
  ensures // No duplicates exist in the result
          forall i, j :: 0 <= i < j < |unique_arr| ==> unique_arr[i] != unique_arr[j]
  ensures // Every element in result comes from the input array
          forall i :: 0 <= i < |unique_arr| ==> unique_arr[i] in arr
  ensures // Every distinct element from input appears in result
          forall x :: x in arr ==> x in unique_arr
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed invariant to maintain subset relationship with full array */
  var sorted_unique := [];
  var i := 0;
  
  while i < |arr|
    invariant 0 <= i <= |arr|
    invariant isSorted(sorted_unique)
    invariant hasNoDuplicates(sorted_unique)
    invariant isSubsetOf(sorted_unique, arr)
    invariant forall x :: x in arr[..i] ==> x in sorted_unique
  {
    if arr[i] !in sorted_unique {
      sorted_unique := insertSorted(sorted_unique, arr[i]);
    }
    i := i + 1;
  }
  
  unique_arr := sorted_unique;
}
// </vc-code>
