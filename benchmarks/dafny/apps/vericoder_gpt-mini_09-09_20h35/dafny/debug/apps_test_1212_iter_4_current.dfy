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
lemma SumWindowSlide(heights: seq<int>, start: int, k: int)
  requires 0 <= start
  requires k > 0
  requires start + k + 1 <= |heights|
  ensures sum_window(heights, start+1, k) == sum_window(heights, start, k) - heights[start] + heights[start + k]
  decreases k
{
  if k == 1 {
    assert sum_window(heights, start, 1) == heights[start];
    assert sum_window(heights, start+1, 1) == heights[start+1];
    assert sum_window(heights, start+1, 1) ==
           sum_window(heights, start, 1) - heights[start] + heights[start + 1];
  } else {
    var s0 := sum_window(heights, start, k);
    var s1 := sum_window(heights, start+1, k-1);
    var s2 := sum_window(heights, start+2, k-1);

    assert s0 == heights[start] + s1;
    assert sum_window(heights, start+1, k) == heights[start+1] + s2;

    SumWindowSlide(heights, start+1, k-1);

    // From the inductive hypothesis:
    assert s2 == s1 - heights[start+1] + heights[start+k];

    // arithmetic simplification
    assert heights[start+1] + s2 == s1 + heights[start+k];
    assert sum_window(heights, start+1, k) == s1 + heights[start+k];

    assert s0 - heights[start] + heights[start+k] == s1 + heights[start+k];
    assert sum_window(heights, start+1, k) == s0 - heights[start] + heights[start + k];
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
  var cur := sum_window(heights, 0, k);
  var best := 0;
  var bestSum := cur;
  var i := 1;
  while i <= n - k
    invariant 0 <= best < i <= n - k + 1
    invariant cur == sum_window(heights, i-1, k)
    invariant bestSum == sum_window(heights, best, k)
    invariant forall s :: 0 <= s < i ==> bestSum <= sum_window(heights, s, k)
    invariant forall s :: 0 <= s < best ==> sum_window(heights, s, k) > bestSum
  {
    var next := cur - heights[i-1] + heights[i + k - 1];
    SumWindowSlide(heights, i-1, k);
    assert next == sum_window(heights, i, k);
    if next < bestSum {
      best := i;
      bestSum := next;
    }
    cur := next;
    i := i + 1;
  }
  result := best + 1;
}
// </vc-code>

