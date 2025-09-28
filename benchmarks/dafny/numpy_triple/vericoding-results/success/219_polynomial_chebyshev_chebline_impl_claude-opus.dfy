// <vc-preamble>
/*
 * Dafny specification for Chebyshev polynomial line function.
 * 
 * This module provides functionality to generate Chebyshev series coefficients
 * for a straight line function of the form off + scl*x, where off is the offset
 * and scl is the scale factor.
 * 
 * Note: This specification uses 'real' type as Dafny's closest approximation
 * to floating-point arithmetic, though it differs semantically from Lean's Float type.
 */

// Method to generate Chebyshev series coefficients for a linear function
// Returns a 2-element array where the first element is the offset coefficient
// and the second element is the scale coefficient, representing off + scl*x
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method chebline(off: real, scl: real) returns (result: array<real>)
  ensures result.Length == 2
  ensures result[0] == off  // First coefficient equals offset parameter
  ensures result[1] == scl  // Second coefficient equals scale parameter
// </vc-spec>
// <vc-code>
{
  result := new real[2];
  result[0] := off;
  result[1] := scl;
}
// </vc-code>
