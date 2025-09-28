// <vc-preamble>
// Method to find indices of all non-zero elements in a sequence
// </vc-preamble>

// <vc-helpers>
function IsIndexInRange(i: nat, a: seq<real>): bool { i < |a| } predicate IsNonZeroElement(a: seq<real>, j: nat) requires 0 <= j < |a| { a[j] != 0.0 } predicate IsResultValid(a: seq<real>, result: seq<nat>) { |result| <= |a| && (forall i :: 0 <= i < |result| ==> 0 <= result[i] < |a| && a[result[i]] != 0.0) && (forall j :: 0 <= j < |a| && a[j] != 0.0 ==> j in result) && (forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j] && result[i] < result[j]) } lemma UniqueSortedIndices(a: seq<real>, result: seq<nat>) requires IsResultValid(a, result) ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j] && result[i] < result[j] { }
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
  result := [];
  var index := 0;
  while index < |a|
    invariant 0 <= index <= |a|
    invariant |result| <= index
    invariant forall k :: 0 <= k < |result| ==> 0 <= result[k] < index && a[result[k]] != 0.0
    invariant forall j :: 0 <= j < index && a[j] != 0.0 ==> j in result
    invariant forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j] && result[i] < result[j]
  {
    if a[index] != 0.0 {
      result := result + [index];
    }
    index := index + 1;
  }
}
// </vc-code>
