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
/* helper modified by LLM (iteration 2): Extend sum_middle_terms by one element on the right */
lemma SumMiddleExtendRight(y: seq<real>, start: int, end: int)
  requires 0 <= start <= end < |y|
  ensures sum_middle_terms(y, start, end + 1) == sum_middle_terms(y, start, end) + y[end]
  decreases end - start
{
  if start < end {
    SumMiddleExtendRight(y, start + 1, end);
  }
}

/* helper modified by LLM (iteration 2): Sum of constant range equals constant times length */
lemma SumMiddleConst(y: seq<real>, start: int, end: int, c: real)
  requires 0 <= start <= end <= |y|
  requires forall i :: start <= i < end ==> y[i] == c
  ensures sum_middle_terms(y, start, end) == c * (end - start) as real
  decreases end - start
{
  if start < end {
    SumMiddleConst(y, start + 1, end, c);
  }
}

/* helper modified by LLM (iteration 2): Non-negativity of sum for non-negative inputs */
lemma SumMiddleNonNeg(y: seq<real>, start: int, end: int)
  requires 0 <= start <= end <= |y|
  requires forall i :: start <= i < end ==> y[i] >= 0.0
  ensures sum_middle_terms(y, start, end) >= 0.0
  decreases end - start
{
  if start < end {
    SumMiddleNonNeg(y, start + 1, end);
  }
}

/* helper modified by LLM (iteration 2): Simple distributivity step over integers-as-reals */
lemma DistRight(c: real, k: int)
  ensures c * (k + 1) as real == c * k as real + c
{
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
  /* code modified by LLM (iteration 2): compute trapezoid sum via loop; remove fragile base-case assertion; provide proofs for constant and non-negative properties */
  var n := |y|;
  if n <= 1 {
    // Since |y| >= 1, we have n == 1 here
    assert n == 1;
    // Set result in a form that matches the exactness postcondition for constants
    result := dx * (n - 1) as real * y[0];
  } else {
    var sum: real := y[0] / 2.0 + y[n - 1] / 2.0;
    var i := 1;
    while i < n - 1
      invariant 1 <= i <= n - 1
      invariant sum == y[0] / 2.0 + sum_middle_terms(y, 1, i) + y[n - 1] / 2.0
      decreases n - 1 - i
    {
      sum := sum + y[i];
      SumMiddleExtendRight(y, 1, i);
      i := i + 1;
    }
    assert i == n - 1;
    result := dx * sum;

    if (forall j :: 0 <= j < n ==> y[j] == y[0]) {
      var c := y[0];
      assert sum == y[0] / 2.0 + sum_middle_terms(y, 1, n - 1) + y[n - 1] / 2.0;
      SumMiddleConst(y, 1, n - 1, c);
      var k := n - 2;
      assert sum == c / 2.0 + c * k as real + c / 2.0;
      assert c / 2.0 + c / 2.0 == c;
      assert sum == c * k as real + c;
      DistRight(c, k);
      assert c * (k + 1) as real == c * k as real + c;
      assert k + 1 == n - 1;
      assert sum == c * (n - 1) as real;
      assert result == dx * (n - 1) as real * c;
    }

    if (forall j :: 0 <= j < n ==> y[j] >= 0.0) {
      assert sum == y[0] / 2.0 + sum_middle_terms(y, 1, n - 1) + y[n - 1] / 2.0;
      SumMiddleNonNeg(y, 1, n - 1);
      assert y[0] >= 0.0 && y[n - 1] >= 0.0;
      assert y[0] / 2.0 >= 0.0 && y[n - 1] / 2.0 >= 0.0;
      assert sum >= 0.0;
      assert result >= 0.0;
    }
  }
}
// </vc-code>
