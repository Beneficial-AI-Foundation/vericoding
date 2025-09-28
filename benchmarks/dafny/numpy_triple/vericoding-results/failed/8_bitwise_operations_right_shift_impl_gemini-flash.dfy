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
/* code modified by LLM (iteration 5): Fixed loop invariant for absolute value of result to handle both positive and negative results in one invariant. */
{
  var res_arr: array<int> := new int[|x1|];
  for i := 0 to |x1|-1
    invariant 0 <= i <= |x1|
    invariant forall j :: 0 <= j < i && x1[j] >= 0 ==> res_arr[j] == x1[j] / Power2(x2[j])
    invariant forall j :: 0 <= j < i && x1[j] < 0 ==> res_arr[j] == ArithmeticRightShift(x1[j], x2[j])
    invariant forall j :: 0 <= j < i && x2[j] == 0 ==> res_arr[j] == x1[j]
    invariant forall j :: 0 <= j < i ==> (x1[j] > 0 ==> res_arr[j] >= 0) && (x1[j] < 0 ==> res_arr[j] <= 0) && (x1[j] == 0 ==> res_arr[j] == 0)
    invariant forall j :: 0 <= j < i ==> (if res_arr[j] >= 0 then res_arr[j] else -res_arr[j]) <= (if x1[j] >= 0 then x1[j] else -x1[j])
  {
    if x1[i] >= 0 {
      res_arr[i] := x1[i] / Power2(x2[i]);
    } else {
      res_arr[i] := ArithmeticRightShift(x1[i], x2[i]);
    }
  }
  return res_arr[..];
}
// </vc-code>
