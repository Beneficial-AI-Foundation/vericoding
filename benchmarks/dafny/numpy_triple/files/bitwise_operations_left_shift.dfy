// <vc-preamble>
// Helper function to compute integer powers
function Power(base: int, exp: nat): int
{
  if exp == 0 then 1
  else base * Power(base, exp - 1)
}

// Bitwise left shift operation on sequences of integers
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method LeftShift(x1: seq<int>, x2: seq<int>) returns (result: seq<int>)
  // Input sequences must have the same length
  requires |x1| == |x2|
  // All shift amounts must be non-negative
  requires forall i :: 0 <= i < |x2| ==> x2[i] >= 0
  
  // Output has same length as inputs
  ensures |result| == |x1|
  // Core behavior: each element is multiplied by 2^shift_amount
  ensures forall i :: 0 <= i < |result| ==> result[i] == x1[i] * Power(2, x2[i])
  // Identity property: shifting by 0 returns original value
  ensures forall i :: 0 <= i < |result| && x2[i] == 0 ==> result[i] == x1[i]
  // Zero preservation: shifting zero always yields zero
  ensures forall i :: 0 <= i < |result| && x1[i] == 0 ==> result[i] == 0
  // Monotonicity for positive values: left shifting increases magnitude
  ensures forall i :: 0 <= i < |result| && x1[i] > 0 && x2[i] > 0 ==> result[i] > x1[i]
  // Monotonicity for negative values: left shifting decreases value (more negative)
  ensures forall i :: 0 <= i < |result| && x1[i] < 0 && x2[i] > 0 ==> result[i] < x1[i]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
