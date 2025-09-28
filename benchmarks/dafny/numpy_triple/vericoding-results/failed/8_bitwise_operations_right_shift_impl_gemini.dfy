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
/* helper modified by LLM (iteration 5): [no changes, retained from previous correct version] */
lemma DivisionShrinksAbs(val: int, divisor: int)
  requires divisor >= 1
  ensures var q := val / divisor;
          (if q >= 0 then q else -q) <= (if val >= 0 then val else -val)
{
  var q := val / divisor;
  var r := val % divisor;
  assert val == q * divisor + r;

  if val >= 0 {
    assert q >= 0;
    // We want to prove q <= val.
    // val - q = q * (divisor - 1) + r.
    // Since q>=0, divisor-1>=0, r>=0, the right side is >= 0.
    // Thus, val - q >= 0, so val >= q.
    assert q * (divisor - 1) >= 0;
    assert r >= 0;
    assert val >= q;
  } else { // val < 0
    assert q < 0;
    // We want to prove -q <= -val, which is q >= val.
    // We want to show val - q <= 0.
    assert r < divisor;
    calc {
      val - q;
    ==
      q * (divisor - 1) + r;
    <= { assert r <= divisor - 1; }
      q * (divisor - 1) + (divisor - 1);
    ==
      (q + 1) * (divisor - 1);
    <= { assert q < 0 ==> q + 1 <= 0; assert divisor - 1 >= 0; }
      0;
    }
    assert val <= q;
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
  /* code modified by LLM (iteration 5): [fixed compilation error: used .Length for array size] */
  var res := new int[|x1|];
  var i := 0;
  while i < |x1|
    invariant 0 <= i <= |x1|
    invariant res.Length == |x1|
    invariant forall j :: 0 <= j < i && x1[j] >= 0 ==> 
      res[j] == x1[j] / Power2(x2[j] as nat)
    invariant forall j :: 0 <= j < i && x1[j] < 0 ==> 
      res[j] == ArithmeticRightShift(x1[j], x2[j] as nat)
    invariant forall j :: 0 <= j < i && x2[j] == 0 ==> 
      res[j] == x1[j]
    invariant forall j :: 0 <= j < i ==>
      (x1[j] > 0 ==> res[j] >= 0) &&
      (x1[j] < 0 ==> res[j] <= 0) &&
      (x1[j] == 0 ==> res[j] == 0)
    invariant forall j :: 0 <= j < i ==>
      (if res[j] >= 0 then res[j] else -res[j]) <= (if x1[j] >= 0 then x1[j] else -x1[j])
  {
    var val := x1[i];
    var shift := x2[i] as nat;
    var divisor := Power2(shift);
    res[i] := val / divisor;
    
    if x2[i] == 0 {
      assert divisor == 1;
    }

    DivisionShrinksAbs(val, divisor);
    
    i := i + 1;
  }
  result := res[..];
}
// </vc-code>
