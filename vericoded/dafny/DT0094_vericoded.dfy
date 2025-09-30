// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method NPY_1_PI() returns (result: real)
  // 1/π is approximately 0.31831...
  ensures 0.31830 < result < 0.31832
  // Basic sanity check: 1/π is between 0 and 1
  ensures 0.0 < result < 1.0
  // More precise bounds for 1/π
  ensures 0.318309 < result < 0.318310
  // 2/π is approximately 0.6366... (double of 1/π)
  ensures 0.6366 < 2.0 * result < 0.6367
  // (1/π)² is approximately 0.10132...
  ensures 0.10131 < result * result < 0.10133
  // 1/(2π) is approximately 0.15915... (half of 1/π)
  ensures 0.15915 < result / 2.0 < 0.15916
  // Mathematical relationship: result * π ≈ 1 (within floating point precision)
  // Using π approximation 3.141592653589793
  ensures 0.99999 < result * 3.141592653589793 < 1.00001
// </vc-spec>
// <vc-code>
{
  result := 0.3183098861837907;
}
// </vc-code>
