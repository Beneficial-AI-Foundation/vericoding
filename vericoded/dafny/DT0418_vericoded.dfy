// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method hermeline(off: real, scl: real) returns (coeffs: seq<real>)
    // Core structural property: always returns exactly 2 coefficients
    ensures |coeffs| == 2
    // Constant term property: first coefficient is always the offset
    ensures coeffs[0] == off
    // Linear term property: second coefficient depends on scale
    ensures scl == 0.0 ==> coeffs[1] == 0.0
    ensures scl != 0.0 ==> coeffs[1] == scl
// </vc-spec>
// <vc-code>
{
  if scl == 0.0 {
    coeffs := [off, 0.0];
  } else {
    coeffs := [off, scl];
  }
}
// </vc-code>
