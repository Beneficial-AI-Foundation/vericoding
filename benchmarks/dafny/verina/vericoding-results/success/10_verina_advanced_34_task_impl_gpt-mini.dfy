// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lemma to relate dp[j]+1 bounds when j<i */
lemma IncBound(j: int, x: int, i: int)
  requires 0 <= j < i
  requires 1 <= x <= j+1
  ensures 1 <= x+1 <= i+1
{
  assert 1 <= x;
  assert x <= j+1;
  assert j < i;
  assert j+1 <= i;
  assert x+1 <= j+2;
  assert j+2 <= i+1;
  assert 1 <= x+1;
  assert x+1 <= i+1;
}

// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubsequence(nums: array<int>) returns (result: int)
    ensures result >= 0
    ensures result <= nums.Length
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Implement LIS using dp with strengthened invariant to ensure result <= nums.Length */
  var n := nums.Length;
  if n == 0 {
    result := 0;
    return;
  }
  var dp := new int[n];
  var ans := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k < i ==> 1 <= dp[k] <= k+1
    invariant 0 <= ans <= n
  {
    dp[i] := 1;
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant forall k :: 0 <= k < i ==> 1 <= dp[k] <= k+1
      invariant 1 <= dp[i] <= i+1
    {
      if nums[j] < nums[i] {
        var temp := dp[j] + 1;
        // Inline proof of bounds for temp: from 1 <= dp[j] <= j+1 and j < i
        assert 1 <= dp[j];
        assert dp[j] <= j+1;
        assert j < i;
        assert j+1 <= i;
        assert dp[j] + 1 <= j+2;
        assert j+2 <= i+1;
        assert temp <= i+1;
        assert 1 <= temp;
        if temp > dp[i] {
          dp[i] := temp;
        }
      }
      j := j + 1;
    }
    if dp[i] > ans { ans := dp[i]; }
    i := i + 1;
  }
  result := ans;
}

// </vc-code>
