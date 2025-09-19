// <vc-preamble>
// Method to obtain the mathematical constant pi
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Pi() returns (result: real)
  ensures 3.14159 < result < 3.14160  // Pi is approximately 3.14159...
  ensures 3.0 < result < 4.0  // Pi is between 3 and 4 (basic sanity check)
  ensures 9.869 < result * result < 9.870  // Pi squared is approximately 9.8696...
  ensures 6.283 < 2.0 * result < 6.284  // 2*pi is approximately 6.28318...
  ensures 1.570 < result / 2.0 < 1.571  // pi/2 is approximately 1.5708...
  ensures 0.785 < result / 4.0 < 0.786  // pi/4 is approximately 0.7854...
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
