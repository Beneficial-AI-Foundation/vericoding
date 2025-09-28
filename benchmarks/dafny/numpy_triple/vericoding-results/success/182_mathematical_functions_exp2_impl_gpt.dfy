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
/* helper modified by LLM (iteration 2): recursive mapping of 2^x over a sequence with correctness ensures */
function MapExp2(x: seq<real>): seq<real>
  ensures |MapExp2(x)| == |x|
  ensures forall i :: 0 <= i < |x| ==> MapExp2(x)[i] == RealPow(2.0, x[i])
  ensures forall i :: 0 <= i < |x| ==> MapExp2(x)[i] > 0.0
{
  if |x| == 0 then []
  else [RealPow(2.0, x[0])] + MapExp2(x[1..])
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
  /* code modified by LLM (iteration 2): implement exp2 by mapping 2^ over the input using helper */
  result := MapExp2(x);
}
// </vc-code>
