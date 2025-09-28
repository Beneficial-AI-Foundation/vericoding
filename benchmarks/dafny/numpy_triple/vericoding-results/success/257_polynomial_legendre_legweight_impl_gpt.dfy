// <vc-preamble>
/*
 * Implementation of the Legendre polynomial weight function.
 * The weight function for Legendre polynomials is constant 1 over the interval [-1, 1].
 * This module provides a method to compute the weight function values for given input points.
 */

// Method to compute the Legendre polynomial weight function
// The weight function is constant 1 for all input values
// </vc-preamble>

// <vc-helpers>
function constOnes(n: nat): seq<real>
  decreases n
  ensures |constOnes(n)| == n
  ensures forall i :: 0 <= i < n ==> constOnes(n)[i] == 1.0
{
  if n == 0 then []
  else constOnes(n - 1) + [1.0]
}
// </vc-helpers>

// <vc-spec>
method legweight(x: seq<real>) returns (result: seq<real>)
  // No preconditions - the weight function is defined for all real values
  requires true
  // The output vector has the same length as the input vector
  ensures |result| == |x|
  // All elements in the result are 1.0, representing the constant weight function
  ensures forall i :: 0 <= i < |result| ==> result[i] == 1.0
// </vc-spec>
// <vc-code>
{
  result := constOnes(|x|);
}
// </vc-code>
