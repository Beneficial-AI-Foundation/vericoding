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
    /* code modified by LLM (iteration 2): [added while loops and invariants to prove postconditions] */
    var n := a.Length;
    if n == 0 {
        result := 0;
        return;
    }

    var dp := new int[n];
    
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < i ==> 1 <= dp[k] && dp[k] <= k + 1
    {
        var max_prev_len := 0;
        var j := 0;
        while j < i
            invariant 0 <= j <= i
            invariant max_prev_len >= 0
            invariant forall k :: 0 <= k < i ==> dp[k] <= k + 1
            invariant max_prev_len <= i
            invariant forall k :: 0 <= k < j ==> (a[k] < a[i] ==> max_prev_len >= dp[k])
        {
            if a[j] < a[i] {
                max_prev_len := IntMax(max_prev_len, dp[j]);
            }
            j := j + 1;
        }
        
        dp[i] := 1 + max_prev_len;
        i := i + 1;
    }

    var max_lis := 0;
    var k := 0;
    while k < n
        invariant 0 <= k <= n
        invariant forall j :: 0 <= j < n ==> dp[j] >= 1 && dp[j] <= n
        invariant forall j :: 0 <= j < k ==> max_lis >= dp[j]
        invariant max_lis <= n
        invariant max_lis >= 0
    {
        max_lis := IntMax(max_lis, dp[k]);
        k := k + 1;
    }
    result := max_lis;
}
// </vc-code>
