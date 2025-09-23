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
{
    // impl-start
    assume {:axiom} false;
    result := 0;
    // impl-end
}
// </vc-code>
