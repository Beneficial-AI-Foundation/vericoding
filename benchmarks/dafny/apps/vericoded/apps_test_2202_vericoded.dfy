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
function SplitScore(A: seq<int>, splitPos: int, p: int): int
    requires 0 < splitPos < |A|
    requires p >= 2
{
    (Sum(A[..splitPos]) % p) + (Sum(A[splitPos..]) % p)
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
    else var rest := MaxSeq(s[1..]); if s[0] > rest then s[0] else rest
}

function MaxSeqOrZero(s: seq<int>): int
{
    if |s| == 0 then 0
    else MaxSeq(s)
}

lemma SplitScoreBound(A: seq<int>, splitPos: int, p: int)
    requires 0 < splitPos < |A|
    requires p >= 2
    requires forall i :: 0 <= i < |A| ==> A[i] >= 1
    ensures 0 <= SplitScore(A, splitPos, p) < 2 * p
{
    assert Sum(A[..splitPos]) % p >= 0;
    assert Sum(A[..splitPos]) % p < p;
    assert Sum(A[splitPos..]) % p >= 0;
    assert Sum(A[splitPos..]) % p < p;
}

lemma MaxSplitScoreBound(A: seq<int>, p: int)
    requires |A| >= 2
    requires p >= 2
    requires forall i :: 0 <= i < |A| ==> A[i] >= 1
    ensures 0 <= MaxSplitScore(A, p) < 2 * p
{
    var scores := seq(|A| - 1, i requires 0 <= i < |A| - 1 => SplitScore(A, i + 1, p));
    assert |scores| > 0;
    
    forall i | 0 <= i < |scores|
        ensures 0 <= scores[i] < 2 * p
    {
        SplitScoreBound(A, i + 1, p);
    }
    
    MaxSeqBounds(scores, 2 * p);
}

lemma MaxSeqBounds(s: seq<int>, bound: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> 0 <= s[i] < bound
    ensures 0 <= MaxSeq(s) < bound
{
    if |s| == 1 {
    } else {
        MaxSeqBounds(s[1..], bound);
    }
}

lemma MaxSeqOrZeroBounds(s: seq<int>, bound: int)
    requires forall i :: 0 <= i < |s| ==> 0 <= s[i] < bound
    requires bound > 0
    ensures 0 <= MaxSeqOrZero(s) < bound
{
    if |s| == 0 {
    } else {
        MaxSeqBounds(s, bound);
    }
}

lemma MaxSeqAppend(s: seq<int>, x: int)
    requires |s| > 0
    ensures MaxSeq(s + [x]) == if x > MaxSeq(s) then x else MaxSeq(s)
{
    if |s| == 1 {
        assert s + [x] == [s[0], x];
    } else {
        assert (s + [x])[0] == s[0];
        assert (s + [x])[1..] == s[1..] + [x];
        MaxSeqAppend(s[1..], x);
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
    MaxSplitScoreBound(A, p);
    
    var maxScore := SplitScore(A, 1, p);
    var i := 2;
    
    while i < N
        invariant 2 <= i <= N
        invariant |seq(i - 1, j requires 0 <= j < i - 1 => SplitScore(A, j + 1, p))| == i - 1
        invariant maxScore == MaxSeq(seq(i - 1, j requires 0 <= j < i - 1 => SplitScore(A, j + 1, p)))
        invariant 0 <= maxScore < 2 * p
    {
        var score := SplitScore(A, i, p);
        
        var prevSeq := seq(i - 1, j requires 0 <= j < i - 1 => SplitScore(A, j + 1, p));
        var newSeq := seq(i, j requires 0 <= j < i => SplitScore(A, j + 1, p));
        
        assert |prevSeq| == i - 1;
        assert |newSeq| == i;
        assert forall j :: 0 <= j < i - 1 ==> prevSeq[j] == newSeq[j];
        assert newSeq[i - 1] == SplitScore(A, i, p);
        assert newSeq == prevSeq + [score];
        
        MaxSeqAppend(prevSeq, score);
        
        if score > maxScore {
            maxScore := score;
        }
        
        assert maxScore == MaxSeq(newSeq);
        
        i := i + 1;
    }
    
    assert i == N;
    assert seq(N - 1, j requires 0 <= j < N - 1 => SplitScore(A, j + 1, p)) == 
           seq(|A| - 1, j requires 0 <= j < |A| - 1 => SplitScore(A, j + 1, p));
    
    result := maxScore;
}
// </vc-code>

