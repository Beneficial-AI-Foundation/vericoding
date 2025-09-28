// <vc-preamble>
// Helper function to compute powers of 2
function Power2(exp: nat): int
  ensures Power2(exp) > 0
{
  if exp == 0 then 1 else 2 * Power2(exp - 1)
}

// Helper function for arithmetic right shift of negative numbers
function ArithmeticRightShift(value: int, shift: nat): int
  requires value < 0
{
  // For negative numbers, we use floor division to maintain sign extension
  value / Power2(shift)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added helper for positive values */
function RightShiftNonNegative(value: int, shift: nat): int
  requires value >= 0
  ensures RightShiftNonNegative(value, shift) == value / Power2(shift)
{
  value / Power2(shift)
}
// </vc-helpers>

// <vc-spec>
method RightShift(x1: seq<int>, x2: seq<int>) returns (result: seq<int>)
  // Input sequences must have the same length
  requires |x1| == |x2|
  // All shift amounts must be non-negative
  requires forall i :: 0 <= i < |x2| ==> x2[i] >= 0
  // Result has same length as inputs
  ensures |result| == |x1|
  // For non-negative values, right shift equals division by 2^shift
  ensures forall i :: 0 <= i < |result| && x1[i] >= 0 ==>
    result[i] == x1[i] / Power2(x2[i])
  // For negative values, use arithmetic right shift (sign extension)
  ensures forall i :: 0 <= i < |result| && x1[i] < 0 ==>
    result[i] == ArithmeticRightShift(x1[i], x2[i])
  // Identity property: shifting by 0 returns original value
  ensures forall i :: 0 <= i < |result| && x2[i] == 0 ==>
    result[i] == x1[i]
  // Sign preservation properties
  ensures forall i :: 0 <= i < |result| ==>
    (x1[i] > 0 ==> result[i] >= 0) &&
    (x1[i] < 0 ==> result[i] <= 0) &&
    (x1[i] == 0 ==> result[i] == 0)
  // Bounded result: absolute value decreases or stays same
  ensures forall i :: 0 <= i < |result| ==>
    if result[i] >= 0 then result[i] <= if x1[i] >= 0 then x1[i] else -x1[i]
    else -result[i] <= if x1[i] >= 0 then x1[i] else -x1[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed result variable declaration and loop implementation */
{
  result := [];
  var i: int := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |result| == i
    invariant forall j :: 0 <= j < i && x1[j] >= 0 ==> result[j] == x1[j] / Power2(x2[j])
    invariant forall j :: 0 <= j < i && x1[j] < 0 ==> result[j] == ArithmeticRightShift(x1[j], x2[j])
  {
    if x1[i] >= 0 {
      result := result + [x1[i] / Power2(x2[i])];
    } else {
      result := result + [ArithmeticRightShift(x1[i], x2[i])];
    }
    i := i + 1;
  }
}
// </vc-code>
