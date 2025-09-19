// <vc-preamble>
// Find the intersection of two arrays, returning sorted unique values present in both
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method intersect1d(ar1: seq<int>, ar2: seq<int>) returns (result: seq<int>)
  ensures // Result contains only values that exist in both input arrays
    forall i :: 0 <= i < |result| ==> result[i] in ar1 && result[i] in ar2
  ensures // Result is sorted in strict ascending order (which ensures uniqueness)
    forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
  ensures // Result is complete - contains all values that appear in both arrays
    forall val :: val in ar1 && val in ar2 ==> val in result
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
