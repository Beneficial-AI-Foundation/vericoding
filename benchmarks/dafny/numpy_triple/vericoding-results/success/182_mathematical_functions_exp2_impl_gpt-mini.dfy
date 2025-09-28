// <vc-preamble>
// Helper function to represent real number exponentiation
function RealPow(base: real, exponent: real): real
    requires base > 0.0
    ensures RealPow(base, exponent) > 0.0
{
    // Abstract function representing mathematical exponentiation
    // In practice, this would implement IEEE 754 floating-point pow behavior
    1.0 // Placeholder to make function compile
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): provide pow2 wrapper for RealPow */
function pow2(x: real): real
    ensures pow2(x) > 0.0
{
    RealPow(2.0, x)
}
// </vc-helpers>

// <vc-spec>
method exp2(x: seq<real>) returns (result: seq<real>)
    // No preconditions - exp2 is defined for all finite real values
    ensures |result| == |x|
    // Each element of result is 2 raised to the power of corresponding input element
    ensures forall i :: 0 <= i < |x| ==> result[i] == RealPow(2.0, x[i])
    // Explicit positivity guarantee
    ensures forall i :: 0 <= i < |x| ==> result[i] > 0.0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): build result sequence using an array and loop with invariants */
  var n := |x|;
  var a := new real[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == pow2(x[j])
    invariant forall j :: 0 <= j < i ==> a[j] > 0.0
  {
    a[i] := pow2(x[i]);
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>
