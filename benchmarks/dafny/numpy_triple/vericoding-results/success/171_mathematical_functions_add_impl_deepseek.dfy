// <vc-preamble>
/*
 * Dafny specification for numpy.add: element-wise addition of two vectors.
 * Implements vector addition where each element of the result is the sum
 * of the corresponding elements from the input vectors.
 */

// Method that adds two vectors element-wise
// Corresponds to numpy.add functionality
// </vc-preamble>

// <vc-helpers>

// Helper predicate to check if all elements at each index satisfy the addition condition
predicate VectorAdditionValid(x1: seq<real>, x2: seq<real>, result: seq<real>)
  requires |x1| == |x2|
{
  |result| == |x1| &&
  (forall i :: 0 <= i < |result| ==> result[i] == x1[i] + x2[i])
}

/* helper modified by LLM (iteration 2): Added length invariant to ensure vector bounds */
lemma VectorAdditionLemma(x1: seq<real>, x2: seq<real>, result: seq<real>, i: int)
  requires |x1| == |x2|
  requires 0 <= i <= |x1|
  requires |result| == i
  requires forall j :: 0 <= j < i ==> result[j] == x1[j] + x2[j]
  ensures i == |x1| ==> VectorAdditionValid(x1, x2, result)
{
}
// </vc-helpers>

// <vc-spec>
method Add(x1: seq<real>, x2: seq<real>) returns (result: seq<real>)
    // Precondition: input vectors must have the same length
    requires |x1| == |x2|
    // Postcondition: result has same length as inputs
    ensures |result| == |x1|
    // Postcondition: each element is sum of corresponding input elements
    ensures forall i :: 0 <= i < |result| ==> result[i] == x1[i] + x2[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed loop invariants and array bounds */
  var length := |x1|;
  result := [];
  
  var i := 0;
  while i < length
    invariant 0 <= i <= length
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == x1[j] + x2[j]
  {
    result := result + [x1[i] + x2[i]];
    i := i + 1;
  }
  
  VectorAdditionLemma(x1, x2, result, i);
}
// </vc-code>
