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
// Helper function to compute element-wise multiplication
function ElementwiseMultiply(x1: seq<real>, x2: seq<real>): seq<real>
  requires |x1| == |x2|
  ensures |ElementwiseMultiply(x1, x2)| == |x1|
  ensures forall i :: 0 <= i < |x1| ==> ElementwiseMultiply(x1, x2)[i] == x1[i] * x2[i]
{
  if |x1| == 0 then []
  else [x1[0] * x2[0]] + ElementwiseMultiply(x1[1..], x2[1..])
}
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
  result := ElementwiseMultiply(x1, x2);
}
// </vc-code>
