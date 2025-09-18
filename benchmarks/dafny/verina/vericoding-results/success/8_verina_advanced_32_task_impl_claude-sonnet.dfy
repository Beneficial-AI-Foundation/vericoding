// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubsequence(numbers: array<int>) returns (result: nat)
    ensures result <= numbers.Length
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed loop invariant bounds by initializing dp[i] before inner loop */
    if numbers.Length == 0 {
        result := 0;
        return;
    }
    
    var dp := new int[numbers.Length];
    var i := 0;
    while i < numbers.Length
        invariant 0 <= i <= numbers.Length
        invariant forall k :: 0 <= k < i ==> dp[k] == 1
    {
        dp[i] := 1;
        i := i + 1;
    }
    
    i := 1;
    while i < numbers.Length
        invariant 1 <= i <= numbers.Length
        invariant forall k :: 0 <= k < numbers.Length ==> 1 <= dp[k] <= k + 1
    {
        var j := 0;
        while j < i
            invariant 0 <= j <= i
            invariant 1 <= dp[i] <= i + 1
            invariant forall k :: 0 <= k < numbers.Length ==> 1 <= dp[k] <= k + 1
        {
            if numbers[j] < numbers[i] && dp[j] + 1 > dp[i] {
                dp[i] := dp[j] + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := 1;
    i := 0;
    while i < numbers.Length
        invariant 0 <= i <= numbers.Length
        invariant forall k :: 0 <= k < numbers.Length ==> 1 <= dp[k] <= numbers.Length
        invariant forall k :: 0 <= k < i ==> dp[k] <= result
        invariant 1 <= result <= numbers.Length
    {
        if dp[i] > result {
            result := dp[i];
        }
        i := i + 1;
    }
}
// </vc-code>
