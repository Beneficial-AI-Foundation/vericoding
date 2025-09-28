// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
predicate IsIncreasing(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}
// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubsequence(nums: array<int>) returns (result: int)
    ensures result >= 0
    ensures result <= nums.Length
// </vc-spec>
// <vc-code>
{
    var n := nums.Length;
    if n == 0 {
        result := 0;
        return;
    }

    var dp := new int[n];

    for i := 0 to n
        invariant forall k :: 0 <= k < i ==> dp[k] >= 1 && dp[k] <= k + 1
    {
        var max_prev_len := 0;
        for j := 0 to i
            invariant max_prev_len >= 0
            invariant forall k :: 0 <= k < j && nums[k] < nums[i] ==> dp[k] <= max_prev_len
            invariant max_prev_len <= i
        {
            if nums[j] < nums[i] && dp[j] > max_prev_len {
                max_prev_len := dp[j];
            }
        }
        dp[i] := 1 + max_prev_len;
    }

    var max_lis := 1;
    for i := 0 to n
        invariant max_lis >= 1 && max_lis <= n
        invariant forall k :: 0 <= k < i ==> dp[k] <= max_lis
    {
        if dp[i] > max_lis {
            max_lis := dp[i];
        }
    }
    result := max_lis;
}
// </vc-code>
