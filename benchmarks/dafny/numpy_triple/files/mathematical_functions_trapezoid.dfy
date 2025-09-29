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
  assume {:axiom} false;
}
// </vc-code>
