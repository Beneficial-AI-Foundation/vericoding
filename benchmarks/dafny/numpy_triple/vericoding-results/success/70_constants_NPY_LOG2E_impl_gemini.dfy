// <vc-preamble>
/*
 * Mathematical constant NPY_LOG2E representing the base 2 logarithm of e.
 * This constant is used in mathematical computations and logarithm base conversions.
 */

// Natural logarithm of 2 constant for mathematical relationships
const LN_2: real := 0.693147180559945309417232121458176568

// Helper function for absolute value since Dafny needs explicit definition
function Abs(x: real): real
{
  if x >= 0.0 then x else -x
}

// Method to obtain the NPY_LOG2E constant value
// </vc-preamble>

// <vc-helpers>
const NPY_LOG2E: real := 1.4426950408889634

lemma lemma_NPY_LOG2E_properties()
  ensures 1.442 < NPY_LOG2E < 1.443
  ensures Abs(NPY_LOG2E - 1.442695040888963407359924681001892137) < 0.000000000000001
  ensures NPY_LOG2E > 0.0
  ensures 1.0 < NPY_LOG2E < 2.0  
  ensures NPY_LOG2E > 1.4426950408 && NPY_LOG2E < 1.4426950409
  ensures Abs(NPY_LOG2E * LN_2 - 1.0) < 0.00000000000001
{
}
// </vc-helpers>

// <vc-spec>
method GetNPY_LOG2E() returns (result: real)
  ensures 1.442 < result < 1.443
  ensures Abs(result - 1.442695040888963407359924681001892137) < 0.000000000000001
  ensures result > 0.0
  ensures 1.0 < result < 2.0  
  ensures result > 1.4426950408 && result < 1.4426950409
  ensures Abs(result * LN_2 - 1.0) < 0.00000000000001
// </vc-spec>
// <vc-code>
{
  lemma_NPY_LOG2E_properties();
  result := NPY_LOG2E;
}
// </vc-code>
