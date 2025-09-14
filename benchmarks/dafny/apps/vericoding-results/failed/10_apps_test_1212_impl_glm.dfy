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
predicate ValidResult(result: int, n: int, k: int, heights: seq<int>)
  requires ValidInput(n, k, heights)
{
  1 <= result <= n-k+1 &&
  (forall start :: 0 <= start <= n-k ==> sum_window(heights, result-1, k) <= sum_window(heights, start, k)) &&
  (forall start :: 0 <= start < result-1 ==> sum_window(heights, start, k) > sum_window(heights, result-1, k))
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, k: int, heights: seq<int>) returns (result: int)
  requires ValidInput(n, k, heights)
  ensures ValidResult(result, n, k, heights)
// </vc-spec>
// <vc-code>
{
  var minIndex := 0;
  var minSum := sum_window(heights, 0, k);

  for i := 1 to n-k+1
    invariant 0 <= minIndex < i
    invariant minSum == sum_window(heights, minIndex, k)
    invariant forall j :: 0 <= j < i ==> minSum <= sum_window(heights, j, k)
    invariant forall j :: 0 <= j < minIndex ==> sum_window(heights, j, k) > minSum
  {
    var currentSum := sum_window(heights, i, k);
    if (currentSum < minSum) 
    {
        minSum := currentSum;
        minIndex := i;
    }
  }

  return minIndex + 1;
}
// </vc-code>

