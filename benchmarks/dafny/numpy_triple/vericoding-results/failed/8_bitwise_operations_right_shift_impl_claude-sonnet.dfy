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
/* helper modified by LLM (iteration 5): fixed Power2 and division lemmas for better postcondition support */
lemma Power2Basic(exp: nat)
  ensures Power2(exp) >= 1
  ensures exp == 0 ==> Power2(exp) == 1
{
}

lemma DivisionByPower2(x: int, shift: nat)
  ensures x >= 0 ==> x / Power2(shift) >= 0
  ensures x < 0 ==> x / Power2(shift) <= 0
  ensures x == 0 ==> x / Power2(shift) == 0
  ensures shift == 0 ==> x / Power2(shift) == x
  ensures x >= 0 ==> x / Power2(shift) <= x
{
  Power2Basic(shift);
  if shift == 0 {
    assert Power2(0) == 1;
  }
}

lemma ArithmeticShiftBounds(value: int, shift: nat)
  requires value < 0
  ensures ArithmeticRightShift(value, shift) <= 0
  ensures shift == 0 ==> ArithmeticRightShift(value, shift) == value
  ensures -ArithmeticRightShift(value, shift) <= -value
{
  Power2Basic(shift);
  if shift == 0 {
    assert Power2(0) == 1;
    assert value / 1 == value;
  } else {
    assert Power2(shift) >= 2;
    assert value / Power2(shift) <= 0;
    assert -value >= 0;
  }
}

lemma PostconditionHelpers(x1: seq<int>, x2: seq<int>, result: seq<int>)
  requires |x1| == |x2| == |result|
  requires forall i :: 0 <= i < |x2| ==> x2[i] >= 0
  requires forall i :: 0 <= i < |result| && x1[i] >= 0 ==> result[i] == x1[i] / Power2(x2[i])
  requires forall i :: 0 <= i < |result| && x1[i] < 0 ==> result[i] == ArithmeticRightShift(x1[i], x2[i])
  ensures forall i :: 0 <= i < |result| && x1[i] >= 0 ==> x1[i] / Power2(x2[i]) >= 0
  ensures forall i :: 0 <= i < |result| && x1[i] < 0 ==> ArithmeticRightShift(x1[i], x2[i]) <= 0
{
  forall i | 0 <= i < |result|
    ensures x1[i] >= 0 ==> x1[i] / Power2(x2[i]) >= 0
    ensures x1[i] < 0 ==> ArithmeticRightShift(x1[i], x2[i]) <= 0
  {
    if x1[i] >= 0 {
      DivisionByPower2(x1[i], x2[i]);
    } else {
      ArithmeticShiftBounds(x1[i], x2[i]);
    }
  }
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
{
  /* code modified by LLM (iteration 5): fixed postcondition verification with explicit case handling */
  result := [];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant |result| == i
    invariant forall j :: 0 <= j < i && x1[j] >= 0 ==> result[j] == x1[j] / Power2(x2[j])
    invariant forall j :: 0 <= j < i && x1[j] < 0 ==> result[j] == ArithmeticRightShift(x1[j], x2[j])
    invariant forall j :: 0 <= j < i && x2[j] == 0 ==> result[j] == x1[j]
    invariant forall j :: 0 <= j < i ==> 
      (x1[j] > 0 ==> result[j] >= 0) &&
      (x1[j] < 0 ==> result[j] <= 0) &&
      (x1[j] == 0 ==> result[j] == 0)
    invariant forall j :: 0 <= j < i ==> 
      if result[j] >= 0 then result[j] <= if x1[j] >= 0 then x1[j] else -x1[j]
      else -result[j] <= if x1[j] >= 0 then x1[j] else -x1[j]
  {
    Power2Basic(x2[i]);
    DivisionByPower2(x1[i], x2[i]);
    
    var shifted: int;
    if x1[i] >= 0 {
      shifted := x1[i] / Power2(x2[i]);
      assert shifted >= 0;
      if x2[i] == 0 {
        assert Power2(0) == 1;
        assert shifted == x1[i];
      }
    } else {
      ArithmeticShiftBounds(x1[i], x2[i]);
      shifted := ArithmeticRightShift(x1[i], x2[i]);
      assert shifted <= 0;
      if x2[i] == 0 {
        assert Power2(0) == 1;
        assert shifted == x1[i];
      }
    }
    
    result := result + [shifted];
    i := i + 1;
  }
  
  PostconditionHelpers(x1, x2, result);
}
// </vc-code>
