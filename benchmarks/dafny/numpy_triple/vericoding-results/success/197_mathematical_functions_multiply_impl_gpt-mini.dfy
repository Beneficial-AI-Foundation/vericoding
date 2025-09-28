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
function ElemProduct(x1: seq<real>, x2: seq<real>, i: int): real
  requires 0 <= i < |x1| && |x1| == |x2|
{
  x1[i] * x2[i]
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
  var n := |x1|;
  var a := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == x1[j] * x2[j]
  {
    a[i] := x1[i] * x2[i];
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>
