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
/* helper modified by LLM (iteration 2): Added lemma to prove Power(2, n) properties for monotonicity */
lemma PowerOfTwoProperties(n: nat)
  requires n > 0
  ensures Power(2, n) > 1
  ensures Power(2, n) >= 2
{
  if n == 1 {
    assert Power(2, 1) == 2;
  } else {
    PowerOfTwoProperties(n - 1);
    assert Power(2, n) == 2 * Power(2, n - 1);
  }
}
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
  /* code modified by LLM (iteration 2): Added lemma calls to help prove monotonicity properties */
  result := [];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == x1[j] * Power(2, x2[j])
    invariant forall j :: 0 <= j < i && x1[j] > 0 && x2[j] > 0 ==> result[j] > x1[j]
    invariant forall j :: 0 <= j < i && x1[j] < 0 && x2[j] > 0 ==> result[j] < x1[j]
  {
    if x2[i] > 0 {
      PowerOfTwoProperties(x2[i]);
    }
    result := result + [x1[i] * Power(2, x2[i])];
    i := i + 1;
  }
}
// </vc-code>
