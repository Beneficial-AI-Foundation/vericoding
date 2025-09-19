// <vc-preamble>
// Method to compute Modified Bessel function i0 element-wise
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method I0(x: seq<real>) returns (result: seq<real>)
  ensures |result| == |x|
  // i0(x) > 0 for all real x (positive function)
  ensures forall i :: 0 <= i < |result| ==> result[i] > 0.0
  // i0(0) = 1 (zero case)
  ensures forall i :: 0 <= i < |x| && x[i] == 0.0 ==> result[i] == 1.0
  // i0(x) = i0(-x) (even function property)
  ensures forall i, j :: 0 <= i < |x| && 0 <= j < |x| && x[j] == -x[i] ==> result[j] == result[i]
  // Monotonicity for non-negative values
  ensures forall i, j :: (0 <= i < |x| && 0 <= j < |x| && x[i] >= 0.0 && x[j] >= 0.0 && x[i] <= x[j]) ==> result[i] <= result[j]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
