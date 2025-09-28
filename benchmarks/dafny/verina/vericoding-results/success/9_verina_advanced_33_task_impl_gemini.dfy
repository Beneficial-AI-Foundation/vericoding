// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function max(a: int, b: int): int {
    if a > b then a else b
}

/* helper modified by LLM (iteration 2): [fix syntax error in quantifier expressions] */
function SeqMax(s: seq<int>): int
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> s[i] <= SeqMax(s)
    ensures exists i :: 0 <= i < |s| && s[i] == SeqMax(s)
{
    if |s| == 1 then s[0]
    else max(s[0], SeqMax(s[1..]))
}
// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubsequence(nums: array<int>) returns (result: int)
    ensures result >= 0
    ensures nums.Length == 0 ==> result == 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): [added invariant to inner loop to prove outer loop invariant] */
    var n := nums.Length;
    if n == 0 {
        result := 0;
        return;
    }

    var dp := new int[n];
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < i ==> dp[k] >= 1
    {
        dp[i] := 1;
        var j := 0;
        while j < i
            invariant 0 <= j <= i
            invariant dp[i] >= 1
            invariant forall k :: 0 <= k < i ==> dp[k] >= 1
        {
            if nums[j] < nums[i] {
                dp[i] := max(dp[i], dp[j] + 1);
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := SeqMax(dp[..]);
}
// </vc-code>
