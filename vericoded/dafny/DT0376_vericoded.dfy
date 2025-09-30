// <vc-preamble>
// Datatype representing a Chebyshev polynomial with coefficients and domain/window intervals
datatype ChebyshevPoly = ChebyshevPoly(
  coef: seq<real>,           // Coefficients in increasing degree order
  domain_min: real,          // Domain interval minimum
  domain_max: real,          // Domain interval maximum  
  window_min: real,          // Window interval minimum
  window_max: real           // Window interval maximum
)

// Method to create a Chebyshev polynomial from coefficients with default domain and window [-1, 1]
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method chebyshev(coef: seq<real>) returns (result: ChebyshevPoly)
  ensures |result.coef| == |coef|  // Length is preserved
  ensures forall i :: 0 <= i < |coef| ==> result.coef[i] == coef[i]  // Element-wise coefficient preservation
  ensures result.domain_min == -1.0  // Default domain minimum
  ensures result.domain_max == 1.0   // Default domain maximum
  ensures result.window_min == -1.0  // Default window minimum
  ensures result.window_max == 1.0   // Default window maximum
  ensures result.domain_min < result.domain_max  // Domain interval is valid
  ensures result.window_min < result.window_max  // Window interval is valid
// </vc-spec>
// <vc-code>
{
  result := ChebyshevPoly(coef, -1.0, 1.0, -1.0, 1.0);
}
// </vc-code>
