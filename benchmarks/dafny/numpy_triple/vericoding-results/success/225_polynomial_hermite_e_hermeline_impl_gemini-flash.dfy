// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// No helpers needed for this problem.
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
  var q0 := off;
  var q1 := 0.0;

  if scl != 0.0 {
    q1 := scl;
  }

  coeffs := [q0, q1];
}
// </vc-code>
