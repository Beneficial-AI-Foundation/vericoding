// <vc-preamble>
// Method to create a polynomial with coefficients in order of increasing degree
// where coefficients[i] represents the coefficient of x^i
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Polynomial(coef: seq<real>, domain: seq<real>, window: seq<real>) returns (result: seq<real>)
  // Domain must be a 2-element sequence representing [domain[0], domain[1]]
  requires |domain| == 2
  // Window must be a 2-element sequence representing [window[0], window[1]] 
  requires |window| == 2
  // Domain interval must be non-degenerate (has positive length)
  requires domain[0] != domain[1]
  // Window interval must be non-degenerate (has positive length)
  requires window[0] != window[1]
  // Result has same length as input coefficients
  ensures |result| == |coef|
  // Critical: Coefficient preservation - each coefficient is preserved exactly
  ensures forall i :: 0 <= i < |coef| ==> result[i] == coef[i]
  // Preserve domain interval non-degeneracy property
  ensures domain[1] - domain[0] != 0.0
  // Preserve window interval non-degeneracy property  
  ensures window[1] - window[0] != 0.0
// </vc-spec>
// <vc-code>
{
  result := coef;
}
// </vc-code>
