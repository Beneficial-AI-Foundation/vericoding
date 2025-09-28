// <vc-preamble>
// Method to compute Hermite series coefficients for a linear function
// Takes an offset (constant term) and scale (linear coefficient)
// Returns a 2-element sequence representing the Hermite coefficients
// </vc-preamble>

// <vc-helpers>

  function hermite_coeff_0(off: real, scl: real): real
    ensures hermite_coeff_0(off, scl) == off
  {
    off
  }

  function hermite_coeff_1(off: real, scl: real): real
    ensures hermite_coeff_1(off, scl) == scl / 2.0
  {
    scl / 2.0
  }

// </vc-helpers>

// <vc-spec>
method hermline(off: real, scl: real) returns (result: seq<real>)
  // Output is exactly 2 elements
  ensures |result| == 2
  // First coefficient is the constant term (offset)
  ensures result[0] == off
  // Second coefficient is half the scale factor (due to H₁(x) = 2x relationship)
  ensures result[1] == scl / 2.0
// </vc-spec>
// <vc-code>
{
  result := [hermite_coeff_0(off, scl), hermite_coeff_1(off, scl)];
}
// </vc-code>
