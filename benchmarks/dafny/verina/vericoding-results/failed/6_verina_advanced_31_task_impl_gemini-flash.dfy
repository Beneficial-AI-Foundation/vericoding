// <vc-preamble>
/* Helper functions for generating subsequences and checking increasing property */
ghost predicate IsSubsequenceOf(subseq: seq<int>, s: seq<int>)
{
    exists indices: seq<int> ::
        |indices| == |subseq| &&
        |indices| >= 0 &&
        (forall i :: 0 <= i < |indices| ==> indices[i] >= 0 && indices[i] < |s|) &&
        (forall i :: 0 <= i < |indices| - 1 ==> indices[i] < indices[i + 1]) &&
        (forall i :: 0 <= i < |subseq| ==> subseq[i] == s[indices[i]])
}

ghost predicate IsStrictlyIncreasing(s: seq<int>)
{
    forall i :: 0 <= i < |s| - 1 ==> s[i] < s[i + 1]
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No change as the helper function passes compilation. */
function GetMax(a: nat, b: nat): nat {
    if a > b then a else b
}
// </vc-helpers>

// <vc-spec>
method LongestIncreasingSubseqLength(xs: array<int>) returns (result: nat)
    ensures
        /* The result is the length of some strictly increasing subsequence */
        exists subseq: seq<int> ::
            IsSubsequenceOf(subseq, xs[..]) && 
            IsStrictlyIncreasing(subseq) && 
            |subseq| == result
    ensures
        /* No strictly increasing subsequence is longer than result */
        forall subseq: seq<int> ::
            (IsSubsequenceOf(subseq, xs[..]) && IsStrictlyIncreasing(subseq)) 
            ==> |subseq| <= result
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed quantifier syntax error in the invariant by changing `(max m' | (condition))` to `(max m' such that (condition) :: expression)`.*/
{
    var n := xs.Length;
    if n == 0 {
        return 0;
    }

    var dp := new array<nat>(n);

    // Initialize dp array. Each element itself is an increasing subsequence of length 1.
    for i := 0 to n - 1 {
        dp[i] := 1;
    }

    // Fill dp array
    for i := 1 to n - 1
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < i ==> dp[k] >= 1
        invariant forall k :: 0 <= k < i ==> dp[k] <= i
        invariant (forall k | 0 <= k < i :: dp[k] == (if exists m | 0 <= m < k && xs[m] < xs[k] then (max m' such that (0 <= m' < k && xs[m'] < xs[k]) :: dp[m']) + 1 else 1))
    {
        for j := 0 to i - 1
            invariant 0 <= j <= i
            invariant dp[i] >= 1
            invariant (forall m | 0 <= m < j && xs[m] < xs[i] :: dp[i] >= dp[m] + 1)
        {
            if xs[i] > xs[j] {
                dp[i] := GetMax(dp[i], dp[j] + 1);
            }
        }
    }

    // Find the maximum value in dp array
    result := 0;
    for i := 0 to n - 1
        invariant 0 <= i <= n
        invariant forall k :: 0 <= k < i ==> result >= dp[k]
    {
        result := GetMax(result, dp[i]);
    }

    return result;
}
// </vc-code>
