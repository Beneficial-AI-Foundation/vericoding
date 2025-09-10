predicate ValidInput(N: int, p: int, A: seq<int>)
{
    N >= 2 && p >= 2 && |A| == N && forall i :: 0 <= i < N ==> A[i] >= 1
}

function MaxSplitScore(A: seq<int>, p: int): int
    requires |A| >= 2
    requires p >= 2
{
    var scores := seq(|A| - 1, i requires 0 <= i < |A| - 1 => SplitScore(A, i + 1, p));
    MaxSeq(scores)
}

// <vc-helpers>
function SplitScore(A: seq<int>, split: int, p: int): int
    requires 0 < split < |A|
    requires p >= 2
{
    var left_sum := Sum(A[..split]);
    var right_sum := Sum(A[split..]);
    (left_sum % p + right_sum % p) % p
}

function Sum(s: seq<int>): int
{
    if |s| == 0 then 0
    else s[0] + Sum(s[1..])
}

function MaxSeq(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else
        var rest_max := MaxSeq(s[1..]);
        if s[0] >= rest_max then s[0] else rest_max
}

lemma SumNonNegative(s: seq<int>)
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures Sum(s) >= 0
{
    if |s| == 0 {
    } else {
        SumNonNegative(s[1..]);
    }
}

lemma SplitScoreBounded(A: seq<int>, split: int, p: int)
    requires 0 < split < |A|
    requires p >= 2
    requires forall i :: 0 <= i < |A| ==> A[i] >= 1
    ensures 0 <= SplitScore(A, split, p) < 2 * p
{
    SumNonNegative(A[..split]);
    SumNonNegative(A[split..]);
    var left_sum := Sum(A[..split]);
    var right_sum := Sum(A[split..]);
    assert left_sum >= 0;
    assert right_sum >= 0;
    assert 0 <= left_sum % p < p;
    assert 0 <= right_sum % p < p;
    assert 0 <= (left_sum % p + right_sum % p) < 2 * p;
}

lemma MaxSeqBounded(s: seq<int>, bound: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> 0 <= s[i] < bound
    ensures 0 <= MaxSeq(s) < bound
{
    if |s| == 1 {
    } else {
        MaxSeqBounded(s[1..], bound);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, p: int, A: seq<int>) returns (result: int)
    requires ValidInput(N, p, A)
    ensures result >= 0
    ensures result < 2 * p
    ensures result == MaxSplitScore(A, p)
// </vc-spec>
// <vc-code>
{
    var scores := seq(N - 1, i requires 0 <= i < N - 1 => SplitScore(A, i + 1, p));
    
    forall i | 0 <= i < |scores|
        ensures 0 <= scores[i] < 2 * p
    {
        SplitScoreBounded(A, i + 1, p);
    }
    
    MaxSeqBounded(scores, 2 * p);
    result := MaxSeq(scores);
}
// </vc-code>

