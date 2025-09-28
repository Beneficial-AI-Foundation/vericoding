// <vc-preamble>
function IntMax(x: int, y: int): int
{
    if x < y then y else x
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubsequence(a: array<int>) returns (result: int)
    ensures result >= 0
    ensures result <= a.Length
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fixed assignment operator syntax error in dp update */
  if a.Length == 0 {
    result := 0;
  } else {
    var dp := new int[a.Length];
    var maxLen := 1;
    dp[0] := 1;
    var i := 1;
    while i < a.Length
      invariant 0 <= i <= a.Length
      invariant 0 <= maxLen <= a.Length
      invariant forall k :: 0 <= k < i ==> 0 < dp[k] <= k+1
      invariant forall k :: 0 <= k < i ==> dp[k] <= i
    {
      var maxSoFar := 1;
      var j := 0;
      while j < i
        invariant 0 <= j <= i
        invariant 1 <= maxSoFar <= i+1
      {
        if a[j] < a[i] {
          maxSoFar := IntMax(maxSoFar, dp[j] + 1);
        }
        j := j + 1;
      }
      dp[i] := maxSoFar;
      if dp[i] > maxLen {
        maxLen := dp[i];
      }
      i := i + 1;
    }
    result := maxLen;
  }
}
// </vc-code>
