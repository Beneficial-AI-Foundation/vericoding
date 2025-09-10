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
lemma sum_window_bounds(heights: seq<int>, start: int, k: int)
  requires 0 <= start
  requires start + k <= |heights|
  requires k > 0
  requires forall i :: 0 <= i < |heights| ==> 1 <= heights[i] <= 100
  ensures k <= sum_window(heights, start, k) <= k * 100
  decreases k
{
  if k == 1 {
    assert heights[start] >= 1 && heights[start] <= 100;
  } else {
    sum_window_bounds(heights, start + 1, k - 1);
    assert heights[start] >= 1 && heights[start] <= 100;
    assert sum_window(heights, start, k) == heights[start] + sum_window(heights, start + 1, k - 1);
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
  var min_sum := sum_window(heights, 0, k);
  var min_pos := 1;
  var current_pos := 1;
  
  while current_pos <= n - k
    invariant 1 <= current_pos <= n - k + 1
    invariant 1 <= min_pos <= current_pos
    invariant min_pos <= n - k + 1
    invariant forall j :: 0 <= j < current_pos ==> sum_window(heights, min_pos - 1, k) <= sum_window(heights, j, k)
    invariant forall j :: 0 <= j < min_pos - 1 ==> sum_window(heights, j, k) > sum_window(heights, min_pos - 1, k)
    invariant min_sum == sum_window(heights, min_pos - 1, k)
  {
    var current_sum := sum_window(heights, current_pos, k);
    if current_sum < min_sum {
      min_sum := current_sum;
      min_pos := current_pos + 1;
    }
    current_pos := current_pos + 1;
  }
  
  result := min_pos;
}
// </vc-code>

