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
  result := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == RealPow(2.0, x[j])
    invariant forall j :: 0 <= j < i ==> result[j] > 0.0
  {
    result := result + [RealPow(2.0, x[i])];
    i := i + 1;
  }
}
// </vc-code>
