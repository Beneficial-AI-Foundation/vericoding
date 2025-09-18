// <vc-preamble>
// Method to create a Legendre series representation of a straight line
// The line is defined as off + scl*x, where off is the y-intercept and scl is the slope
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method legline(off: real, scl: real) returns (result: array<real>)
  // The result is always a 2-element array containing the Legendre coefficients
  ensures result.Length == 2
  // The first coefficient represents the constant term (off)
  ensures result[0] == off
  // The second coefficient represents the linear term coefficient (scl)  
  ensures result[1] == scl
  // Ensures the result array is freshly allocated
  ensures fresh(result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
