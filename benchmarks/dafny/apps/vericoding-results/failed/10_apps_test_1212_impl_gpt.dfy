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
  var s := 0;
  var bestStart := 0;
  var bestSum := sum_window(heights, 0, k);
  while s < n - k
    invariant 0 <= s <= n - k
    invariant 0 <= bestStart <= s
    invariant k > 0
    invariant s + k <= |heights|
    invariant bestSum == sum_window(heights, bestStart, k)
    invariant forall start :: 0 <= start <= s ==> (sum_window(heights, bestStart, k) <= sum_window(heights, start, k))
    invariant forall start :: 0 <= start < bestStart ==> (sum_window(heights, start, k) > sum_window(heights, bestStart, k))
    decreases n - k - s
  {
    var next := s + 1;
// </vc-code>

