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
function sum_window_helper(heights: seq<int>, start: int, k: int): (sum: int)
  requires 0 <= start <= |heights| - k
  requires 0 < k <= |heights|
  ensures sum == sum_window(heights, start, k)
  decreases k
{
  if k == 1 then 
    heights[start]
  else 
    heights[start] + sum_window_helper(heights, start + 1, k - 1)
}

lemma sum_window_lemma(heights: seq<int>, start1: int, start2: int, k: int)
  requires 0 <= start1 < start2
  requires start2 + k <= |heights|
  requires k > 0
  ensures sum_window_helper(heights, start1, k) >= sum_window_helper(heights, start2, k) ==>
    sum_window_helper(heights, start1, k) > sum_window_helper(heights, start2, k) || 
    (start1 + 1 < start2 && sum_window_helper(heights, start1 + 1, k) == sum_window_helper(heights, start2, k))
{
  if k == 1 {
    calc {
      sum_window_helper(heights, start1, k);
      heights[start1];
    }
    calc {
      sum_window_helper(heights, start2, k);
      heights[start2];
    }
  } else {
    calc {
      sum_window_helper(heights, start1, k);
      heights[start1] + sum_window_helper(heights, start1 + 1, k - 1);
    }
    calc {
      sum_window_helper(heights, start2, k);
      heights[start2] + sum_window_helper(heights, start2 + 1, k - 1);
    }
    if heights[start1] > heights[start2] {
    } else if heights[start1] < heights[start2] {
    } else {
      sum_window_lemma(heights, start1 + 1, start2 + 1, k - 1);
    }
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
  var min_sum := 0;
  var min_start := 0;
  
  min_sum := sum_window_helper(heights, 0, k);
  min_start := 1;
  
  var i := 1;
  while i <= n - k
    invariant 1 <= min_start <= n - k + 1
    invariant 1 <= i <= n - k + 1
    invariant min_start == i || min_start < i
    invariant forall j :: 0 <= j < min_start - 1 ==> sum_window_helper(heights, j, k) > sum_window_helper(heights, min_start - 1, k)
    invariant forall j :: 0 <= j < i ==> sum_window_helper(heights, min_start - 1, k) <= sum_window_helper(heights, j, k)
  {
    var current_sum := sum_window_helper(heights, i, k);
    if current_sum < min_sum {
      min_sum := current_sum;
      min_start := i + 1;
      sum_window_lemma(heights, min_start - 2, i, k);
    } else {
      sum_window_lemma(heights, min_start - 1, i, k);
    }
    i := i + 1;
  }
  
  result := min_start;
}
// </vc-code>

