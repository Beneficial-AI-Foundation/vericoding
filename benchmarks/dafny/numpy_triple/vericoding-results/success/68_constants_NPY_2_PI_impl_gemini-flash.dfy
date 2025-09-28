// <vc-preamble>
/*
 * Mathematical constant NPY_2_PI representing 2/π ≈ 0.6366197723675813
 * This file defines the specification for the mathematical constant 2 divided by π,
 * with precise bounds and mathematical properties.
 */

// Method to obtain the mathematical constant 2/π
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed semicolon from const declaration */
const PI: real := 3.141592653589793
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
/* code modified by LLM (iteration 2): Implemented calculation for NPY_2_PI */
{
  result := 2.0 / PI;
}
// </vc-code>
