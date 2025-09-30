// <vc-preamble>
// Mathematical constant π for reference in specifications
const PI: real := 3.141592653589793238462643383279502884
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method NPY_PI_4() returns (result: real)
  // No preconditions required for accessing a mathematical constant
  // Exact value for π/4
  ensures result == 0.785398163397448309615660845819875721
  // Mathematical properties of π/4
  ensures result > 0.785 && result < 0.786
  ensures result * 4.0 > 3.141 && result * 4.0 < 3.142
  // π/4 is positive and less than 1
  ensures result > 0.0
  ensures result < 1.0
// </vc-spec>
// <vc-code>
{
  result := 0.785398163397448309615660845819875721;
}
// </vc-code>
