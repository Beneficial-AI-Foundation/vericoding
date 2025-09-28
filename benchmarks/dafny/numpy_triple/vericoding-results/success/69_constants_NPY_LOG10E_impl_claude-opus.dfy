// <vc-preamble>
// Method to compute/return the base 10 logarithm of e
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method NPY_LOG10E() returns (result: real)
  // No preconditions needed for a mathematical constant
  // Use approximation bounds instead of exact equality for floating-point semantics
  ensures 0.434294481903251827651128918916605081 < result < 0.434294481903251827651128918916605083
  // Mathematical property: the result is the base 10 logarithm of e
  // This means 10^result should equal e (approximately 2.718281828...)
  // and result * ln(10) should equal 1 (fundamental logarithm property)
  // Note: Cannot directly express power/logarithm function relationships in Dafny postcondition
  // The value is positive since e > 1 and log₁₀ is increasing
  ensures result > 0.0
  // The value is less than 1 since e < 10
  ensures result < 1.0
  // More precise bounds based on mathematical properties
  ensures 0.4 < result < 0.5
// </vc-spec>
// <vc-code>
{
  result := 0.434294481903251827651128918916605082;
}
// </vc-code>
