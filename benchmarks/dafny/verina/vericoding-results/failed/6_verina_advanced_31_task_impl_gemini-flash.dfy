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
/* helper modified by LLM (iteration 2): original implementation caused syntax errors in the invariants */
function max(a: nat, b: nat): nat { if a >= b then a else b }
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
/* code modified by LLM (iteration 2): Fixed syntax errors in the invariants and re-formatted the loop structure. Originally, there were compilation problems with `max i | 0 <= i < j :: lis[i]` in the invariant. Replaced with simpler overallMaxLen check. */
{
    var n := xs.Length;
    if n == 0 {
        return 0;
    }

    // lis[i] stores the length of the longest increasing subsequence ending at index i
    var lis: array<nat> := new array<nat>(n);
    for i := 0 to n - 1 {
        lis[i] := 1;
    }

    var overallMaxLen := 1;

    for j := 1 to n - 1
        invariant 0 <= j <= n
        invariant forall k :: 0 <= k < j ==> 1 <= lis[k] <= j // lis[k] is at least 1 and at most k+1 (which is less than or equal to j if k < j)
        invariant 1 <= overallMaxLen <= j
        invariant forall k :: 0 <= k < j ==> overallMaxLen >= lis[k]
    {
        for i := 0 to j - 1
            invariant 0 <= i < j
            invariant forall k :: 0 <= k < i ==> 1 <= lis[k] // lis[k] is at least 1
            invariant 1 <= lis[j] <= j // lis[j] is at least 1 and at most j+1 (which is less than or equal to j-1, plus 1)
        {
            if xs[j] > xs[i] {
                lis[j] := max(lis[j], lis[i] + 1);
            }
        }
        overallMaxLen := max(overallMaxLen, lis[j]);
    }

    result := overallMaxLen;
}
// </vc-code>
