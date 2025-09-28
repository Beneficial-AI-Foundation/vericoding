// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// No helper functions needed for this implementation
// </vc-helpers>

// <vc-spec>
method NPY_SQRT1_2() returns (result: real)
    // The result is the square root of 1/2, so its square equals 0.5
    ensures result * result == 0.5
    // The result is positive
    ensures result > 0.0
    // The result equals 1 divided by the square root of 2
    ensures result * result * 2.0 == 1.0
    // The result is approximately the known mathematical value
    ensures result >= 0.707106781186547524400844362104849038
    ensures result <= 0.707106781186547524400844362104849040
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): return mathematical constant value directly */
  result := 0.707106781186547524400844362104849039;
}
// </vc-code>
