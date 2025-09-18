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
/* helper modified by LLM (iteration 5): fixed syntax error in method signature */
lemma EmptySubseqProperties(s: seq<int>)
    ensures IsSubsequenceOf([], s)
    ensures IsStrictlyIncreasing([])
{
    assert exists indices: seq<int> :: indices == [] &&
        |indices| == |[]| &&
        |indices| >= 0 &&
        (forall i :: 0 <= i < |indices| ==> indices[i] >= 0 && indices[i] < |s|) &&
        (forall i :: 0 <= i < |indices| - 1 ==> indices[i] < indices[i + 1]) &&
        (forall i :: 0 <= i < |[]| ==> [][i] == s[indices[i]]);
}

lemma SingletonSubseqProperties(s: seq<int>, idx: int)
    requires 0 <= idx < |s|
    ensures IsSubsequenceOf([s[idx]], s)
    ensures IsStrictlyIncreasing([s[idx]])
{
    var indices := [idx];
    assert |indices| == |[s[idx]]| == 1;
    assert indices[0] == idx && 0 <= idx < |s|;
    assert [s[idx]][0] == s[indices[0]];
}

method ConstructWitness(xs: array<int>, dp: array<int>, maxLen: int) returns (witness: seq<int>)
    requires xs.Length == dp.Length
    requires maxLen >= 1 ==> xs.Length > 0
    requires maxLen >= 0
    ensures |witness| == maxLen
    ensures maxLen > 0 ==> IsSubsequenceOf(witness, xs[..])
    ensures maxLen > 0 ==> IsStrictlyIncreasing(witness)
    ensures maxLen == 0 ==> witness == []
{
    if maxLen == 0 {
        witness := [];
        return;
    }
    
    // Find an index with the maximum length
    var maxIdx := 0;
    var i := 1;
    while i < xs.Length
        invariant 1 <= i <= xs.Length
        invariant 0 <= maxIdx < xs.Length
    {
        if dp[i] > dp[maxIdx] {
            maxIdx := i;
        }
        i := i + 1;
    }
    
    witness := [xs[maxIdx]];
    SingletonSubseqProperties(xs[..], maxIdx);
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
    /* code modified by LLM (iteration 5): fixed witness property access */
    var n := xs.Length;
    if n == 0 {
        result := 0;
        EmptySubseqProperties(xs[..]);
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
        {
            if xs[j] < xs[i] && dp[j] + 1 > dp[i] {
                dp[i] := dp[j] + 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    result := 1;
    i := 1;
    while i < n
        invariant 1 <= i <= n
        invariant result >= 1
        invariant exists k :: 0 <= k < n && dp[k] >= result
    {
        if dp[i] > result {
            result := dp[i];
        }
        i := i + 1;
    }
    
    // Construct and verify witness
    var witness := ConstructWitness(xs, dp, result);
    
    // For the case when result > 0, witness properties are ensured by ConstructWitness
    // For result == 0 case (which can't happen since n > 0 and result >= 1), handle separately
    assert result > 0;
    assert |witness| == result;
    assert IsSubsequenceOf(witness, xs[..]);
    assert IsStrictlyIncreasing(witness);
}
// </vc-code>
