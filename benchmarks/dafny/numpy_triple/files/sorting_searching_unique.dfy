// <vc-preamble>
// Method to find unique elements in an array, removing duplicates and sorting
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method unique(ar: seq<real>) returns (result: seq<real>)
  // No preconditions - works on any input array
  ensures |result| <= |ar|
  // The result is sorted in ascending order
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
  // No duplicates in the result (defines uniqueness)
  ensures forall i, j :: 0 <= i < j < |result| ==> result[i] != result[j]
  // Every element in result comes from the input array
  ensures forall i :: 0 <= i < |result| ==> result[i] in ar
  // Every distinct element from input appears exactly once in result  
  ensures forall x :: x in ar ==> x in result
  ensures forall x :: x in result ==> x in ar
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
