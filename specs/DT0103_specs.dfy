// <vc-preamble>
/*
 * Mathematical constant representing the square root of 2 (√2).
 * Provides the value 1.414213562373095048801688724209698079 with 
 * appropriate mathematical properties and precision guarantees.
 */

// Helper function for absolute value since Dafny doesn't have built-in abs for reals
function Abs(x: real): real
{
  if x >= 0.0 then x else -x
}

// Method that returns the mathematical constant for square root of 2
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method NPY_SQRT2() returns (result: real)
  // No preconditions - this is a mathematical constant
  ensures result > 0.0
  // Use tolerance-based approximation instead of exact equality
  ensures Abs(result * result - 2.0) < 1e-15
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
