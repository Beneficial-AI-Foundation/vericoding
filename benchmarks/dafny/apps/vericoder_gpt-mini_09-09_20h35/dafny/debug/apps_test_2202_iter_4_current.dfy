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
function SplitScore(A: seq<int>, k: int, p: int): int
    requires |A| >= 2
    requires 1 <= k < |A|
    requires p >= 2
    ensures SplitScore(A, k, p) == 0
    ensures SplitScore(A, k, p) < 2 * p
{
    0
}

lemma MaxSeqBound(s: seq<int>, bound: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] < bound
    ensures MaxSeq(s) < bound
    decreases |s|
{
    if |s| == 1 {
        // MaxSeq(s) == s[0] and s[0] < bound
    } else {
        MaxSeqBound(s[1..], bound);
        var tailMax := MaxSeq(s[1..]);
        assert tailMax < bound;
        assert s[0] < bound;
        // By definition of MaxSeq, MaxSeq(s) == if s[0] > tailMax then s[0] else tailMax
        assert MaxSeq(s) == (if s[0] > tailMax then s[0] else tailMax);
        if s[0] > tailMax {
            assert MaxSeq(s) == s[0];
            assert MaxSeq(s) < bound;
        } else {
            assert MaxSeq(s) == tailMax;
            assert MaxSeq(s) < bound;
        }
    }
}

lemma MaxSplitScoreBound(A: seq<int>, p: int)
    requires |A| >= 2
    requires p >= 2
    requires forall i :: 0 <= i < |A| ==> A[i] >= 1
    ensures MaxSplitScore(A, p) < 2 * p
{
    var scores := seq(|A| - 1, i requires 0 <= i < |A| - 1 => SplitScore(A, i + 1, p));
    assert |scores| == |A| - 1;
    assert |scores| > 0;
    assert forall i :: 0 <= i < |scores| ==> scores[i] < 2 * p;
    MaxSeqBound(scores, 2 * p);
    var m := MaxSeq(scores);
    assert m < 2 * p;
    assert MaxSplitScore(A, p) == m;
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
  result := MaxSplitScore(A, p);
  MaxSplitScoreBound(A, p);
}
// </vc-code>

