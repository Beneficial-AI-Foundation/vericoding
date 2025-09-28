// <vc-preamble>
/*
 * Dafny specification for numpy.true_divide: Element-wise division of vectors.
 * 
 * True division of the inputs, element-wise, always returning floating point results.
 * The result is computed element-wise as x1[i] / x2[i] for all valid indices i.
 * Division by zero is prevented through preconditions requiring non-zero divisors.
 */

// Type alias to represent floating point numbers (modeled as reals in Dafny)
type float = real

// Method implementing element-wise vector division
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method TrueDivide(x1: seq<float>, x2: seq<float>) returns (result: seq<float>)
  // Preconditions: vectors must have same length and no zero divisors
  requires |x1| == |x2|
  requires forall i :: 0 <= i < |x2| ==> x2[i] != 0.0
  
  // Postconditions: result properties and mathematical relationships
  ensures |result| == |x1|  // Preserves vector length
  ensures forall i :: 0 <= i < |result| ==> result[i] == x1[i] / x2[i]  // Element-wise division
  ensures forall i :: 0 <= i < |result| ==> result[i] == x1[i] * (1.0 / x2[i])  // Alternative form
  ensures forall i :: 0 <= i < |result| ==> x2[i] * result[i] == x1[i]  // Inverse relationship
// </vc-spec>
// <vc-code>
{
  result := seq(|x1|, i requires 0 <= i < |x1| => x1[i] / x2[i]);
}
// </vc-code>
