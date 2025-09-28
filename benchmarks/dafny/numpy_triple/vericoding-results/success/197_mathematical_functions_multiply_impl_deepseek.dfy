// <vc-preamble>
/*
 * Element-wise multiplication of numerical vectors.
 * 
 * This module provides functionality equivalent to numpy.multiply,
 * performing element-wise multiplication of two input vectors to
 * produce a result vector where each element is the product of
 * the corresponding elements from the input vectors.
 */

// Method to multiply two vectors element-wise
// Equivalent to numpy.multiply functionality
// </vc-preamble>

// <vc-helpers>
function multiplyElement(a: real, b: real): real { a * b }

/* helper modified by LLM (iteration 2): keep element multiplication function */
// </vc-helpers>

// <vc-spec>
method Multiply(x1: seq<real>, x2: seq<real>) returns (result: seq<real>)
  // Precondition: input vectors must have the same length
  requires |x1| == |x2|
  
  // Postconditions:
  // 1. Result vector has the same length as input vectors
  ensures |result| == |x1|
  ensures |result| == |x2|
  
  // 2. Element-wise correctness: result[i] = x1[i] * x2[i] for all valid indices
  ensures forall i :: 0 <= i < |result| ==> result[i] == x1[i] * x2[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fix loop invariants to ensure verification */
  result := [];
  var i := 0;
  while i < |x1|
    invariant i <= |x1| && |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == x1[j] * x2[j]
  {
    result := result + [x1[i] * x2[i]];
    i := i + 1;
  }
}
// </vc-code>
