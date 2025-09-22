// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
