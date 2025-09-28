// <vc-preamble>
/*
 * Mathematical constant NPY_2_PI representing 2/π ≈ 0.6366197723675813
 * This file defines the specification for the mathematical constant 2 divided by π,
 * with precise bounds and mathematical properties.
 */

// Method to obtain the mathematical constant 2/π
// </vc-preamble>

// <vc-helpers>

function square(x: real): real { x * x }
function cube(x: real): real { x * x * x }
function reciprocal(x: real): real requires x != 0.0 { 1.0 / x }
const PI: real := 3.141592653589793  /* helper modified by LLM (iteration 3): fixed const declaration syntax */
lemma pi_bounds() ensures 3.14159 < PI < 3.14160 {}
lemma two_pi_reciprocal_equivalence() ensures 2.0 / PI == reciprocal(PI) * 2.0 {}

// </vc-helpers>

// <vc-spec>
method NPY_2_PI() returns (result: real)
  ensures 0.6366 < result < 0.6367                    // Approximate value bounds
  ensures 0.0 < result < 1.0                          // Basic sanity check: 2/π is between 0 and 1
  ensures 0.636619 < result < 0.636620                // More precise bounds
  ensures 1.999 < result * 3.14159 < 2.001            // Relationship with π: result * π ≈ 2
  ensures 0.405 < result * result < 0.406             // Square of 2/π bounds
  ensures 0.318 < result / 2.0 < 0.319                // Half value gives 1/π bounds
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): use proper PI constant with assert verification */
  pi_bounds();
  two_pi_reciprocal_equivalence();
  result := 2.0 / PI;
  
  // Verification assertions
  assert 0.6366 < result < 0.6367;
  assert 0.0 < result < 1.0;
  assert 0.636619 < result < 0.636620;
  assert 1.999 < result * 3.14159 < 2.001;
  assert 0.405 < result * result < 0.406;
  assert 0.318 < result / 2.0 < 0.319;
}
// </vc-code>
