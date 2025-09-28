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
/* helper modified by LLM (iteration 2): Added lemmas to prove monotonicity properties */
lemma PowerGreaterThanOne(exp: nat)
  requires exp > 0
  ensures Power(2, exp) > 1
{
  if exp == 1 {
    assert Power(2, 1) == 2;
  } else {
    PowerGreaterThanOne(exp - 1);
    assert Power(2, exp) == 2 * Power(2, exp - 1);
    assert Power(2, exp - 1) > 1;
    assert Power(2, exp) > 2;
  }
}

lemma PositiveMultiplicationIncreases(x: int, y: int)
  requires x > 0 && y > 1
  ensures x * y > x
{
  assert y >= 2;
  assert x * y >= x * 2;
  assert x * 2 == x + x;
  assert x + x > x;
}

lemma NegativeMultiplicationDecreases(x: int, y: int)
  requires x < 0 && y > 1
  ensures x * y < x
{
  assert y >= 2;
  assert x * y <= x * 2;
  assert x * 2 == x + x;
  assert x < 0;
  assert x + x < x;
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
  /* code modified by LLM (iteration 2): Added lemma calls to prove monotonicity postconditions */
  result := [];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == x1[j] * Power(2, x2[j])
    invariant forall j :: 0 <= j < i && x1[j] > 0 && x2[j] > 0 ==> result[j] > x1[j]
    invariant forall j :: 0 <= j < i && x1[j] < 0 && x2[j] > 0 ==> result[j] < x1[j]
  {
    var shifted_value := x1[i] * Power(2, x2[i]);
    
    if x1[i] > 0 && x2[i] > 0 {
      PowerGreaterThanOne(x2[i]);
      PositiveMultiplicationIncreases(x1[i], Power(2, x2[i]));
    }
    
    if x1[i] < 0 && x2[i] > 0 {
      PowerGreaterThanOne(x2[i]);
      NegativeMultiplicationDecreases(x1[i], Power(2, x2[i]));
    }
    
    result := result + [shifted_value];
    i := i + 1;
  }
}
// </vc-code>
