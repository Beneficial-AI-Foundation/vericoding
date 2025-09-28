// <vc-preamble>
function sum_squares(p: int, a: seq<int>): int
{
    if |a| == 0 then 0
    else (p - a[0]) * (p - a[0]) + sum_squares(p, a[1..])
}

predicate ValidInput(n: int, a: seq<int>)
{
    n >= 1 && n <= 100 && |a| == n && 
    forall i :: 0 <= i < |a| ==> -100 <= a[i] <= 100
}

predicate IsOptimalCost(result: int, a: seq<int>)
{
    result >= 0 &&
    exists p :: -100 <= p <= 100 && result == sum_squares(p, a) &&
    forall p :: -100 <= p <= 100 ==> result <= sum_squares(p, a)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes, passing through */
function sum_squares_range(p: int, a: seq<int>, start: int, end: int): int
decreases end - start
{
    if start >= end then 0
    else (p - a[start]) * (p - a[start]) + sum_squares_range(p, a, start + 1, end)
}

lemma SumSquaresRangeProperty(p: int, a: seq<int>, start: int, end: int)
  requires start <= end
  requires end <= |a|
  requires 0 <= start
  ensures sum_squares_range(p, a, start, end) == sum_squares(p, a[start..end])
{
  if start < end {
    calc {
      sum_squares_range(p, a, start, end);
      (p - a[start]) * (p - a[start]) + sum_squares_range(p, a, start + 1, end);
      (p - a[start]) * (p - a[start]) + sum_squares(p, a[start+1..end]);
      sum_squares(p, a[start..end]);
    }
  }
}

// </vc-helpers>

// <vc-spec>
method solve(n: int, a: seq<int>) returns (result: int)
    requires ValidInput(n, a)
    ensures IsOptimalCost(result, a)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed ambiguous boolean expression with parentheses */
{
  var min_cost := sum_squares(-100, a); // Initialize with the cost for p = -100
  var optimal_p := -100; // Initialize with p = -100

  var p := -100;
  while p <= 100
    invariant -100 <= p <= 101
    invariant (exists p_iter :: -100 <= p_iter < p && min_cost == sum_squares(p_iter, a)) || (p == -100 && min_cost == sum_squares(-100, a))
    invariant forall p_iter :: -100 <= p_iter < p ==> min_cost <= sum_squares(p_iter, a)
    invariant -100 <= optimal_p < p
  {
    var current_cost := 0;
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant current_cost == sum_squares_range(p, a, 0, i)
    {
      current_cost := current_cost + (p - a[i]) * (p - a[i]);
      i := i + 1;
    }
    SumSquaresRangeProperty(p, a, 0, n);
    assert current_cost == sum_squares(p, a);

    if current_cost < min_cost {
      min_cost := current_cost;
      optimal_p := p;
    }
    p := p + 1;
  }

  result := min_cost;
}
// </vc-code>
