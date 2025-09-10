function sum_window(heights: seq<int>, start: int, k: int): int
  requires 0 <= start
  requires start + k <= |heights|
  requires k > 0
  decreases k
{
  if k == 1 then heights[start]
  else heights[start] + sum_window(heights, start + 1, k - 1)
}

predicate ValidInput(n: int, k: int, heights: seq<int>)
{
  1 <= k <= n && |heights| == n && forall i :: 0 <= i < n ==> 1 <= heights[i] <= 100
}

predicate ValidResult(result: int, n: int, k: int, heights: seq<int>)
  requires ValidInput(n, k, heights)
{
  1 <= result <= n-k+1 &&
  forall start :: 0 <= start <= n-k ==> 
    sum_window(heights, result-1, k) <= sum_window(heights, start, k) &&
  forall start :: 0 <= start < result-1 ==>
    sum_window(heights, start, k) > sum_window(heights, result-1, k)
}

// <vc-helpers>
lemma SumWindowBounds(heights: seq<int>, start: int, k: int)
  requires 0 <= start
  requires start + k <= |heights|
  requires k > 0
  requires forall i :: 0 <= i < |heights| ==> 1 <= heights[i] <= 100
  ensures k <= sum_window(heights, start, k) <= 100 * k
  decreases k
{
  if k == 1 {
    assert sum_window(heights, start, k) == heights[start];
  } else {
    SumWindowBounds(heights, start + 1, k - 1);
    assert sum_window(heights, start, k) == heights[start] + sum_window(heights, start + 1, k - 1);
  }
}

lemma MinSumExists(n: int, k: int, heights: seq<int>) returns (min_start: int)
  requires ValidInput(n, k, heights)
  ensures 0 <= min_start <= n - k
  ensures forall start :: 0 <= start <= n - k ==> 
    sum_window(heights, min_start, k) <= sum_window(heights, start, k)
{
  min_start := 0;
  var i := 1;
  while i <= n - k
    invariant 1 <= i <= n - k + 1
    invariant 0 <= min_start <= n - k
    invariant forall start :: 0 <= start < i ==> 
      sum_window(heights, min_start, k) <= sum_window(heights, start, k)
  {
    if sum_window(heights, i, k) < sum_window(heights, min_start, k) {
      min_start := i;
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, heights: seq<int>) returns (result: int)
  requires ValidInput(n, k, heights)
  ensures ValidResult(result, n, k, heights)
// </vc-spec>
// <vc-code>
{
  var min_start := 0;
  var min_sum := sum_window(heights, 0, k);
  var i := 1;
  
  while i <= n - k
    invariant 1 <= i <= n - k + 1
    invariant 0 <= min_start <= n - k
    invariant min_sum == sum_window(heights, min_start, k)
    invariant forall start :: 0 <= start < i ==> (min_sum <= sum_window(heights, start, k))
    invariant forall start :: 0 <= start < min_start ==> (sum_window(heights, start, k) > min_sum)
  {
    var current_sum := sum_window(heights, i, k);
    if current_sum < min_sum {
      min_start := i;
      min_sum := current_sum;
    }
    i := i + 1;
  }
  
  result := min_start + 1;
}
// </vc-code>

