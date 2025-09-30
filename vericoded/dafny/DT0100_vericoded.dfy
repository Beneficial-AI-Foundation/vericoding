// <vc-preamble>
// Method that returns the mathematical constant π/2
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method NPY_PI_2() returns (result: real)
  // No preconditions needed for a mathematical constant
  ensures 1.5707 < result < 1.5708  // π/2 is approximately 1.5708...
  ensures 1.0 < result < 2.0        // Basic sanity check: π/2 is between 1 and 2
  ensures 2.467 < result * result < 2.468  // π/2 squared is approximately 2.4674...
  ensures 3.141 < 2.0 * result < 3.142     // 2*(π/2) should be approximately π
  ensures 0.785 < result / 2.0 < 0.786     // (π/2)/2 = π/4 is approximately 0.7854...
  ensures 4.712 < 3.0 * result < 4.713     // 3*(π/2) = 3π/2 is approximately 4.7124...
  ensures 6.283 < 4.0 * result < 6.284     // 4*(π/2) = 2π is approximately 6.2832...
// </vc-spec>
// <vc-code>
{
  result := 1.5707963267948966;
}
// </vc-code>
