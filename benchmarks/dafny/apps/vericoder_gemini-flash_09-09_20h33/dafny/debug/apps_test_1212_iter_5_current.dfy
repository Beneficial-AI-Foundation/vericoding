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
function sum_window_helper(heights: seq<int>, start: int, k: int): int
  requires 0 <= start
  requires start + k <= |heights|
  requires k > 0
  decreases k
{
  if k == 1 then heights[start]
  else heights[start] + sum_window_helper(heights, start + 1, k - 1)
}

predicate ValidInputPredicate(n: int, k: int, heights: seq<int>)
{
  1 <= k <= n && |heights| == n && (forall i :: 0 <= i < n ==> 1 <= heights[i] <= 100)
}

predicate ValidResultPredicate(result: int, n: int, k: int, heights: seq<int>)
  requires ValidInputPredicate(n, k, heights)
{
  1 <= result <= n-k+1 &&
  (forall start :: 0 <= start <= n-k ==> 
    sum_window_helper(heights, result-1, k) <= sum_window_helper(heights, start, k)) &&
  (forall start :: 0 <= start < result-1 ==>
    sum_window_helper(heights, start, k) > sum_window_helper(heights, result-1, k))
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, heights: seq<int>) returns (result: int)
  requires ValidInput(n, k, heights)
  ensures ValidResult(result, n, k, heights)
// </vc-spec>
// <vc-code>
{
  var min_sum := sum_window_helper(heights, 0, k);
  var min_idx := 0;

  var current_sum := min_sum;
  for i := 1 to n - k
    invariant 0 <= i <= n - k
    invariant 0 <= min_idx < i || (i == 1 && min_idx == 0)
    invariant min_sum == sum_window_helper(heights, min_idx, k)
    invariant forall j :: 0 <= j < i ==> sum_window_helper(heights, min_idx, k) <= sum_window_helper(heights, j, k)
    invariant current_sum == sum_window_helper(heights, i-1, k)
    invariant i-1+k <= |heights|
  {
    current_sum := current_sum - heights[i-1] + heights[i+k-1]; // current_sum is now sum for window starting at i
    if current_sum < min_sum {
      min_sum := current_sum;
      min_idx := i;
    }
  }
  result := min_idx + 1;
}
// </vc-code>

