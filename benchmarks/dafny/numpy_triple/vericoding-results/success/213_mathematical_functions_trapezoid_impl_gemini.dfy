// <vc-preamble>
// Method to compute numerical integration using composite trapezoidal rule
// Ghost function to represent the mathematical result of trapezoid integration
ghost function trapezoid_result(y: seq<real>, dx: real): real
  requires |y| >= 1
  requires dx > 0.0
{
  if |y| == 1 then 0.0
  else
    dx * (y[0]/2.0 + (sum_middle_terms(y, 1, |y|-1)) + y[|y|-1]/2.0)
}

// Ghost function to sum the middle terms (not including first and last)
ghost function sum_middle_terms(y: seq<real>, start: int, end: int): real
  requires 0 <= start <= end <= |y|
  decreases end - start
{
  if start >= end then 0.0
  else y[start] + sum_middle_terms(y, start + 1, end)
}
// </vc-preamble>

// <vc-helpers>
lemma LemmaSumMiddleConstant(y: seq<real>, c: real, start: int, end: int)
  requires 0 <= start <= end <= |y|
  requires forall i :: start <= i < end ==> y[i] == c
  ensures sum_middle_terms(y, start, end) == (end - start) as real * c
  decreases end - start
{
  if start < end {
    LemmaSumMiddleConstant(y, c, start + 1, end);
  }
}

lemma LemmaSumMiddleNonNegative(y: seq<real>, start: int, end: int)
  requires 0 <= start <= end <= |y|
  requires forall i :: start <= i < end ==> y[i] >= 0.0
  ensures sum_middle_terms(y, start, end) >= 0.0
  decreases end - start
{
  if start < end {
    LemmaSumMiddleNonNegative(y, start + 1, end);
  }
}

/* helper modified by LLM (iteration 2): added lemma to prove an inductive property of sum_middle_terms */
lemma LemmaSumMiddleAppend(y: seq<real>, start: int, end: int)
  requires 0 <= start < end <= |y|
  ensures sum_middle_terms(y, start, end) == sum_middle_terms(y, start, end - 1) + y[end - 1]
  decreases end - start
{
  if start < end - 1 {
    LemmaSumMiddleAppend(y, start + 1, end);
  }
}
// </vc-helpers>

// <vc-spec>
method trapezoid(y: seq<real>, dx: real) returns (result: real)
  requires |y| >= 1  // Need at least one data point
  requires dx > 0.0    // Spacing must be positive
  ensures
    // For constant functions, trapezoid rule gives exact result
    (forall i :: 0 <= i < |y| ==> y[i] == y[0]) ==>
      result == dx * (|y| - 1) as real * y[0]
  ensures
    // Monotonicity: non-negative inputs yield non-negative result
    (forall i :: 0 <= i < |y| ==> y[i] >= 0.0) ==> result >= 0.0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added lemma call to prove loop invariant maintenance */
  if |y| <= 1 {
    result := 0.0;
  } else {
    var sum_y : real := y[0]/2.0 + y[|y|-1]/2.0;
    var i := 1;
    while i < |y| - 1
      invariant 1 <= i <= |y| - 1
      invariant sum_y == y[0]/2.0 + y[|y|-1]/2.0 + sum_middle_terms(y, 1, i)
    {
      LemmaSumMiddleAppend(y, 1, i + 1);
      sum_y := sum_y + y[i];
      i := i + 1;
    }

    if (forall k :: 0 <= k < |y| ==> y[k] == y[0]) {
      LemmaSumMiddleConstant(y, y[0], 1, |y| - 1);
    }
    if (forall k :: 0 <= k < |y| ==> y[k] >= 0.0) {
      LemmaSumMiddleNonNegative(y, 1, |y| - 1);
    }

    result := dx * sum_y;
  }
}
// </vc-code>
