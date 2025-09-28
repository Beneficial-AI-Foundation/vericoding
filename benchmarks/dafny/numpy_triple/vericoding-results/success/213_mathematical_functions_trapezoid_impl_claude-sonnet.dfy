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
lemma sum_middle_terms_constant(y: seq<real>, start: int, end: int, c: real)
  requires 0 <= start <= end <= |y|
  requires forall i :: start <= i < end ==> y[i] == c
  ensures sum_middle_terms(y, start, end) == (end - start) as real * c
  decreases end - start
{
  if start >= end {
  } else {
    sum_middle_terms_constant(y, start + 1, end, c);
  }
}

lemma sum_middle_terms_nonnegative(y: seq<real>, start: int, end: int)
  requires 0 <= start <= end <= |y|
  requires forall i :: start <= i < end ==> y[i] >= 0.0
  ensures sum_middle_terms(y, start, end) >= 0.0
  decreases end - start
{
  if start >= end {
  } else {
    sum_middle_terms_nonnegative(y, start + 1, end);
  }
}

/* helper modified by LLM (iteration 2): added lemma to help prove loop invariant maintenance */
lemma sum_middle_terms_extend(y: seq<real>, start: int, mid: int, end: int)
  requires 0 <= start <= mid <= end <= |y|
  ensures sum_middle_terms(y, start, end) == sum_middle_terms(y, start, mid) + sum_middle_terms(y, mid, end)
  decreases end - start
{
  if start >= mid {
  } else {
    sum_middle_terms_extend(y, start + 1, mid, end);
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
  /* code modified by LLM (iteration 2): added lemma call to prove invariant maintenance */
  if |y| == 1 {
    result := 0.0;
  } else {
    var middle_sum := 0.0;
    var i := 1;
    while i < |y| - 1
      invariant 1 <= i <= |y| - 1
      invariant middle_sum == sum_middle_terms(y, 1, i)
    {
      middle_sum := middle_sum + y[i];
      i := i + 1;
      sum_middle_terms_extend(y, 1, i-1, i);
    }
    
    result := dx * (y[0]/2.0 + middle_sum + y[|y|-1]/2.0);
    
    // Prove constant function property
    if forall j :: 0 <= j < |y| ==> y[j] == y[0] {
      sum_middle_terms_constant(y, 1, |y|-1, y[0]);
    }
    
    // Prove non-negativity
    if forall j :: 0 <= j < |y| ==> y[j] >= 0.0 {
      sum_middle_terms_nonnegative(y, 1, |y|-1);
    }
  }
}
// </vc-code>
