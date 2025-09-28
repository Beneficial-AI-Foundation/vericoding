// <vc-preamble>
// Method to return the Euler-Mascheroni constant γ
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method EulerGamma() returns (result: real)
  // Sanity check: euler_gamma is within reasonable bounds
  ensures 0.577 < result < 0.578
  // Mathematical property: euler_gamma is approximately 0.5772156649015329
  ensures 0.5772156649015329 - 0.000000000000001 < result < 0.5772156649015329 + 0.000000000000001
  // Mathematical property: euler_gamma is positive
  ensures result > 0.0
  // Mathematical property: euler_gamma is less than 1
  ensures result < 1.0
  // Mathematical property: euler_gamma is between 0.5 and 0.6
  ensures 0.5 < result < 0.6
  // More precise bounds for numerical calculations
  ensures 0.5772156649 < result < 0.5772156650
  // Mathematical property: 1 - euler_gamma is positive (approximately 0.4228...)
  ensures 0.0 < 1.0 - result < 0.5
// </vc-spec>
// <vc-code>
{
  // The Euler-Mascheroni constant (γ) is a fundamental mathematical constant.
  // Since Dafny's real type is designed for mathematical reals and not
  // floating-point numbers, we can directly assign its known value.
  // The problem's postconditions specify various bounds that this value must satisfy.
  // The most precise value provided in the ensures clauses is used for direct assignment.
  result := 0.5772156649015329;
}
// </vc-code>
