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

// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, heights: seq<int>) returns (result: int)
  requires ValidInput(n, k, heights)
  ensures ValidResult(result, n, k, heights)
// </vc-spec>
// <vc-code>
{
  var min_index := 0;
  var min_sum := sum_window(heights, 0, k);
  var i := 1;
  while i <= n - k
    invariant 0 <= min_index <= i
    invariant min_index <= n - k
    invariant min_sum == sum_window(heights, min_index, k)
    invariant forall j :: 0 <= j < i ==> min_sum <= sum_window(heights, j, k)
    invariant forall j :: 0 <= j < min_index ==> sum_window(heights, j, k) > min_sum
  {
    var current_sum := sum_window(heights, i, k);
    if current_sum < min_sum {
      min_sum := current_sum;
      min_index := i;
    }
    i := i + 1;
  }
  result := min_index + 1;
}
// </vc-code>

