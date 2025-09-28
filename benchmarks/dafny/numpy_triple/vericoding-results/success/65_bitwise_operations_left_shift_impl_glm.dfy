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
lemma Power2IsPositive(n: nat)
  ensures Power(2, n) >= 1
{
  if n == 0 {
  } else {
    calc {
      Power(2, n);
      == 2 * Power(2, n-1);
      >= 2 * 1;   // Power(2, n-1) >= 1 by induction
      >= 1;
    }
  }
}

lemma Power2AtLeast2(n: nat)
  requires n > 0
  ensures Power(2, n) >= 2
{
  if n == 1 {
    assert Power(2,1) == 2;
  } else {
    calc {
      Power(2, n);
      == 2 * Power(2, n-1);
      >= 2 * 1;   // Power(2, n-1) >= 1 by Power2IsPositive
      == 2;
    }
  }
}

lemma MultIncreasesPositive(x: int, k: int)
  requires x > 0 && k >= 2
  ensures x * k > x
{
  calc {
    x * k;
    >= x * 2;
    == 2 * x;
    > x;
  }
}

lemma MultDecreasesNegative(x: int, k: int)
  requires x < 0 && k >= 2
  ensures x * k < x
{
  calc {
    x * k;
    <= x * 2;
    == 2 * x;
    < x;
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
/* code modified by LLM (iteration 2): fixed sequence construction using sequence appending */
{
  var n := |x1|;
  var temp: seq<int> := [];
  for i := 0 to n
    invariant 0 <= i <= n
    invariant |temp| == i
    invariant forall j :: 0 <= j < i ==> temp[j] == x1[j] * Power(2, x2[j])
    invariant forall j :: 0 <= j < i && x2[j] == 0 ==> temp[j] == x1[j]
    invariant forall j :: 0 <= j < i && x1[j] == 0 ==> temp[j] == 0
    invariant forall j :: 0 <= j < i && x2[j] > 0 && x1[j] > 0 ==> temp[j] > x1[j]
    invariant forall j :: 0 <= j < i && x2[j] > 0 && x1[j] < 0 ==> temp[j] < x1[j]
  {
    var newVal := x1[i] * Power(2, x2[i]);
    if x2[i] > 0 {
      if x1[i] > 0 {
        Power2AtLeast2(x2[i]);
        MultIncreasesPositive(x1[i], Power(2, x2[i]));
      } else if x1[i] < 0 {
        Power2AtLeast2(x2[i]);
        MultDecreasesNegative(x1[i], Power(2, x2[i]));
      }
    }
    temp := temp + [newVal];
  }
  result := temp;
}
// </vc-code>
