// <vc-preamble>
// Method to find indices of all non-zero elements in a sequence
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method FlatNonZero(a: seq<real>) returns (result: seq<nat>)
  // No preconditions - accepts any sequence of reals
  ensures |result| <= |a|
  // All indices in result are valid and point to non-zero elements
  ensures forall i :: 0 <= i < |result| ==> 0 <= result[i] < |a| && a[result[i]] != 0.0
  // All non-zero elements have their indices in result
  ensures forall j :: 0 <= j < |a| && a[j] != 0.0 ==> j in result
  // Result contains no duplicate indices
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
  // Result indices are sorted in ascending order
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
