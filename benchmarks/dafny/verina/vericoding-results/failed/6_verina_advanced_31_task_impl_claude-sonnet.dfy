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
/* helper modified by LLM (iteration 5): complete witness construction in lemmas */
function MaxLengthIncreasingSubseq(s: seq<int>, i: int): nat
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i == |s| then 0
    else
        var withCurrent := 1 + MaxLengthIncreasingSubseqStartingWith(s, i + 1, s[i]);
        var withoutCurrent := MaxLengthIncreasingSubseq(s, i + 1);
        if withCurrent > withoutCurrent then withCurrent else withoutCurrent
}

function MaxLengthIncreasingSubseqStartingWith(s: seq<int>, i: int, minVal: int): nat
    requires 0 <= i <= |s|
    decreases |s| - i
{
    if i == |s| then 0
    else if s[i] <= minVal then MaxLengthIncreasingSubseqStartingWith(s, i + 1, minVal)
    else
        var withCurrent := 1 + MaxLengthIncreasingSubseqStartingWith(s, i + 1, s[i]);
        var withoutCurrent := MaxLengthIncreasingSubseqStartingWith(s, i + 1, minVal);
        if withCurrent > withoutCurrent then withCurrent else withoutCurrent
}

ghost function GetOptimalSubseq(s: seq<int>, i: int): seq<int>
    requires 0 <= i <= |s|
    ensures IsSubsequenceOf(GetOptimalSubseq(s, i), s[i..]) 
    ensures IsStrictlyIncreasing(GetOptimalSubseq(s, i))
    ensures |GetOptimalSubseq(s, i)| == MaxLengthIncreasingSubseq(s, i)
    decreases |s| - i
{
    if i == |s| then []
    else
        var withCurrent := 1 + MaxLengthIncreasingSubseqStartingWith(s, i + 1, s[i]);
        var withoutCurrent := MaxLengthIncreasingSubseq(s, i + 1);
        if withCurrent > withoutCurrent then
            [s[i]] + GetOptimalSubseqStartingWith(s, i + 1, s[i])
        else
            GetOptimalSubseq(s, i + 1)
}

ghost function GetOptimalSubseqStartingWith(s: seq<int>, i: int, minVal: int): seq<int>
    requires 0 <= i <= |s|
    ensures IsStrictlyIncreasing(GetOptimalSubseqStartingWith(s, i, minVal))
    ensures forall x :: x in GetOptimalSubseqStartingWith(s, i, minVal) ==> x > minVal
    ensures |GetOptimalSubseqStartingWith(s, i, minVal)| == MaxLengthIncreasingSubseqStartingWith(s, i, minVal)
    decreases |s| - i
{
    if i == |s| then []
    else if s[i] <= minVal then GetOptimalSubseqStartingWith(s, i + 1, minVal)
    else
        var withCurrent := 1 + MaxLengthIncreasingSubseqStartingWith(s, i + 1, s[i]);
        var withoutCurrent := MaxLengthIncreasingSubseqStartingWith(s, i + 1, minVal);
        if withCurrent > withoutCurrent then
            [s[i]] + GetOptimalSubseqStartingWith(s, i + 1, s[i])
        else
            GetOptimalSubseqStartingWith(s, i + 1, minVal)
}

lemma MaximalityLemma(s: seq<int>, subseq: seq<int>)
    requires IsSubsequenceOf(subseq, s) && IsStrictlyIncreasing(subseq)
    ensures |subseq| <= MaxLengthIncreasingSubseq(s, 0)
{
    MaximalityLemmaHelper(s, subseq, 0);
}

lemma MaximalityLemmaHelper(s: seq<int>, subseq: seq<int>, i: int)
    requires 0 <= i <= |s|
    requires IsSubsequenceOf(subseq, s) && IsStrictlyIncreasing(subseq)
    ensures |subseq| <= MaxLengthIncreasingSubseq(s, i)
    decreases |s| - i
{
    if i == |s| {
        assert subseq == [];
    } else {
        MaximalityLemmaHelper(s, subseq, i + 1);
    }
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
{
    /* code modified by LLM (iteration 5): use ghost functions for witness construction */
    result := MaxLengthIncreasingSubseq(xs[..], 0);
    
    // First postcondition is satisfied by GetOptimalSubseq
    ghost var witness := GetOptimalSubseq(xs[..], 0);
    assert IsSubsequenceOf(witness, xs[..]);
    assert IsStrictlyIncreasing(witness);
    assert |witness| == result;
    
    // Second postcondition
    forall subseq: seq<int> | IsSubsequenceOf(subseq, xs[..]) && IsStrictlyIncreasing(subseq)
        ensures |subseq| <= result
    {
        MaximalityLemma(xs[..], subseq);
    }
}
// </vc-code>
