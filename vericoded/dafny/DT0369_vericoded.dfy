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
/* helper modified by LLM (iteration 3): Append lemma for sum_middle_terms (relates end to end-1) */
lemma SumMiddleAppend(y: seq<real>, start: int, end: int)
  requires 0 <= start < end <= |y|
  ensures sum_middle_terms(y, start, end) == sum_middle_terms(y, start, end - 1) + y[end - 1]
  decreases end - start
{
  if start + 1 == end {
    // base case: sum over a single element
    assert sum_middle_terms(y, start, end) == y[start] + sum_middle_terms(y, start + 1, end);
    assert sum_middle_terms(y, start + 1, end) == 0.0;
    assert sum_middle_terms(y, start, end - 1) == 0.0;
    assert y[start] == y[end - 1];
    return;
  }
  // inductive step
  assert sum_middle_terms(y, start, end) == y[start] + sum_middle_terms(y, start + 1, end);
  SumMiddleAppend(y, start + 1, end);
  assert sum_middle_terms(y, start + 1, end) == sum_middle_terms(y, start + 1, end - 1) + y[end - 1];
  assert sum_middle_terms(y, start, end - 1) == y[start] + sum_middle_terms(y, start + 1, end - 1);
  assert y[start] + sum_middle_terms(y, start + 1, end - 1) + y[end - 1] == sum_middle_terms(y, start, end - 1) + y[end - 1];
  assert sum_middle_terms(y, start, end) == sum_middle_terms(y, start, end - 1) + y[end - 1];
}

/* helper modified by LLM (iteration 3): Sum middle terms for constant sequence */
lemma SumMiddleConstant(y: seq<real>, start: int, end: int)
  requires 0 <= start <= end <= |y|
  requires |y| >= 1
  requires forall i :: 0 <= i < |y| ==> y[i] == y[0]
  ensures sum_middle_terms(y, start, end) == (end - start) as real * y[0]
  decreases end - start
{
  if start >= end {
    return;
  }
  SumMiddleConstant(y, start + 1, end);
  assert sum_middle_terms(y, start, end) == y[start] + sum_middle_terms(y, start + 1, end);
  assert y[start] == y[0];
  assert sum_middle_terms(y, start + 1, end) == (end - (start + 1)) as real * y[0];
  assert y[start] + (end - (start + 1)) as real * y[0] == (end - start) as real * y[0];
}

/* helper modified by LLM (iteration 3): Sum middle terms non-negativity */
lemma SumMiddleNonneg(y: seq<real>, start: int, end: int)
  requires 0 <= start <= end <= |y|
  requires forall i :: 0 <= i < |y| ==> y[i] >= 0.0
  ensures sum_middle_terms(y, start, end) >= 0.0
  decreases end - start
{
  if start >= end {
    return;
  }
  SumMiddleNonneg(y, start + 1, end);
  assert sum_middle_terms(y, start, end) == y[start] + sum_middle_terms(y, start + 1, end);
  assert y[start] >= 0.0;
  assert sum_middle_terms(y, start + 1, end) >= 0.0;
  assert y[start] + sum_middle_terms(y, start + 1, end) >= 0.0;
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
/* code modified by LLM (iteration 3): compute trapezoid and prove properties using helper lemmas */
{
  var n := |y|;
  if n == 1 {
    result := 0.0;
    // Prove postconditions for the single-sample case
    if forall k :: 0 <= k < n ==> y[k] == y[0] {
      assert (n - 1) as real * y[0] == 0.0;
      assert result == dx * (n - 1) as real * y[0];
    }
    if forall k :: 0 <= k < n ==> y[k] >= 0.0 {
      assert result >= 0.0;
    }
    return;
  }

  var s := 0.0;
  var i := 1;
  while i < n - 1
    invariant 1 <= i <= n - 1
    invariant s == sum_middle_terms(y, 1, i)
    decreases n - 1 - i
  {
    var old_s := s;
    var old_i := i;
    s := old_s + y[old_i];
    i := old_i + 1;
    // Use lemma to relate sum up to i with sum up to i-1 plus y[i-1]
    SumMiddleAppend(y, 1, i);
    // From the loop invariant before update we have old_s == sum_middle_terms(y,1,old_i)
    assert old_s == sum_middle_terms(y, 1, old_i);
    assert sum_middle_terms(y, 1, i) == sum_middle_terms(y, 1, old_i) + y[old_i];
    assert s == sum_middle_terms(y, 1, i);
  }

  result := dx * (y[0] / 2.0 + s + y[n - 1] / 2.0);

  // Prove exactness for constant sequences (n >= 2)
  if n >= 2 && (forall k :: 0 <= k < n ==> y[k] == y[0]) {
    SumMiddleConstant(y, 1, n - 1);
    assert s == sum_middle_terms(y, 1, n - 1);
    assert s == (n - 2) as real * y[0];
    assert y[n - 1] == y[0];
    assert y[0] / 2.0 + s + y[n - 1] / 2.0 == (n - 1) as real * y[0];
    assert result == dx * (n - 1) as real * y[0];
  }

  // Prove non-negativity when all samples are non-negative (n >= 2)
  if n >= 2 && (forall k :: 0 <= k < n ==> y[k] >= 0.0) {
    SumMiddleNonneg(y, 1, n - 1);
    assert s == sum_middle_terms(y, 1, n - 1);
    assert s >= 0.0;
    assert y[0] / 2.0 + s + y[n - 1] / 2.0 >= 0.0;
    assert dx > 0.0;
    assert result >= 0.0;
  }
}

// </vc-code>
