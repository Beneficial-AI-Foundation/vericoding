// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM人們 (iteration 5): No helpers needed for this implementation */
// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubsequence(nums: array<int>) returns (result: int)
    ensures result >= 0
    ensures result <= nums.Length
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Added assertions in inner loop to fuese help verifier prove loop invariants */
  var dp := new int[nums.Length];
  var i := 0;
  while i < nums.Length
    invariant 0 <= i <= nums.Length
    invariant forall m :: 0 <= m < i ==> 1 <= dp[m] <= m + 1
  {
    dp[i] := 1;
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      invariant dp[i] >= 1 && dp[i] <= i + 1
      invariant forall n :: 0 <= n < i ==> 1 <= dp[n] <= n + 1
    {
      if nums[j] < nums[i] && dp[j] + 1 > dp[i] {
        assert j < i;
        assert j + 1 <= i;
        assert i >= j + 1;
        assert dp[j] <= j + 1;
        assert dp[j] + 1 <= i + 1;
        dp[i] := dp[j] + 1;
      }
      j := j + 1;
    }
    assert 1 <= dp[i] <= i + 1;
    i := i + 1;
  }
  result := 0;
  var k := 0;
  while k < nums.Length
    invariant 0 <= k <= nums.Length
    invariant result >= 0
    invariant result <= nums.Length
  {
    if dp[k] > result {
      result := dp[k];
    }
    k := k + 1;
  }
  assert result >= 0;
}
// </vc-code>
