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
lemma window_sum_monotonic(heights: seq<int>, start1: int, start2: int, k: int)
  requires 0 <= start1 <= start2
  requires start2 + k <= |heights|
  requires k > 0
  ensures sum_window(heights, start1, k) >= sum_window(heights, start2, k)
  decreases k
{
  if k == 1 {
    // Base case: single element windows
    // Dafny needs help understanding the ordering
    assert start1 <= start2;
    assert heights[start1] >= heights[start2];
  } else {
    // Recursive case: prove the tail and add the heads
    assert start1 + 1 <= start2 + 1;
    window_sum_monotonic(heights, start1 + 1, start2 + 1, k - 1);
    assert heights[start1] >= heights[start2];
  }
}

lemma window_sum_strict_monotonic(heights: seq<int>, start1: int, start2: int, k: int)
  requires 0 <= start1 < start2
  requires start2 + k <= |heights|
  requires k > 0
  requires heights[start1] > heights[start2]
  ensures sum_window(heights, start1, k) > sum_window(heights, start2, k)
  decreases k
{
  if k == 1 {
    // Base case: heights[start1] > heights[start2]
  } else {
    assert heights[start1] > heights[start2];
    // Need to ensure the recursive call preconditions hold
    assert start1 + 1 <= start2 + 1;
    assert start1 + 1 <= start2 + 1; // Not necessarily strict
    if start1 + 1 < start2 + 1 {
      // If we still have strict inequality, use the lemma
      window_sum_strict_monotonic(heights, start1 + 1, start2 + 1, k - 1);
    } else {
      // When start1 + 1 == start2 + 1, we're done since heads were different
      assert start1 == start2; // Contradiction with start1 < start2
    }
    // heights[start1] > heights[start2] contributes to the inequality
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
  result := 1;
  var min_sum := sum_window(heights, 0, k);
  var i := 1;
  
  while i <= n - k
    invariant 1 <= result <= i + 1
    invariant 0 <= i <= n - k + 1
    invariant forall j :: 0 <= j < i ==> min_sum <= sum_window(heights, j, k)
    invariant i > 0 ==> sum_window(heights, result - 1, k) == min_sum
    invariant forall j :: 0 <= j < result - 1 ==> sum_window(heights, j, k) > min_sum
  {
    var current_sum := sum_window(heights, i, k);
    if current_sum < min_sum {
      result := i + 1;
      min_sum := current_sum;
    } else if current_sum == min_sum {
      // Maintain result as the smallest index with minimal sum
      // No need to update since we want the first occurrence
    }
    i := i + 1;
    
    // Update the invariant for the new i
    if current_sum < min_sum {
      assert forall j :: 0 <= j < i ==> min_sum <= sum_window(heights, j, k);
    }
  }
  
  // Post-loop assertion to satisfy ValidResult
  assert forall start :: 0 <= start <= n-k ==> min_sum <= sum_window(heights, start, k);
  assert forall start :: 0 <= start < result-1 ==> sum_window(heights, start, k) > min_sum;
}
// </vc-code>

