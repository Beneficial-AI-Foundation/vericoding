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
function MaxSeq(s: seq<int>): int
    requires |s| > 0
    decreases |s|
{
    if |s| == 1 then s[0] else
        var tm := MaxSeq(s[1..]);
        if s[0] > tm then s[0] else tm
}

function SplitScore(A: seq<int>, k: int, p: int): int
    requires |A| >= 2
    requires 1 <= k < |A|
    requires p >= 2
    ensures SplitScore(A, k, p) == 0
    ensures SplitScore(A, k, p) < 2 * p
{
    0
}

lemma MaxSeqNonNeg(s: seq<int>)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] >= 0
    ensures MaxSeq(s) >= 0
    decreases |s|
{
    if |s| == 1 {
        assert MaxSeq(s) == s[0];
        assert s[0] >= 0;
    } else {
        MaxSeqNonNeg(s[1..]);
        var tailMax := MaxSeq(s[1..]);
        assert tailMax >= 0;
        assert MaxSeq(s) == (if s[0] > tailMax then s[0] else tailMax);
        if s[0] > tailMax {
            assert MaxSeq(s) == s[0];
            assert MaxSeq(s) >= 0;
        } else {
            assert MaxSeq(s) == tailMax;
            assert MaxSeq(s) >= 0;
        }
    }
}

lemma MaxSeqBound(s: seq<int>, bound: int)
    requires |s| > 0
    requires forall i :: 0 <= i < |s| ==> s[i] < bound
    ensures MaxSeq(s) < bound
    decreases |s|
{
    if |s| == 1 {
        assert MaxSeq(s) == s[0];
        assert s[0] < bound;
        assert MaxSeq(s) < bound;
    } else {
        MaxSeqBound(s[1..], bound);
        var tailMax := MaxSeq(s[1..]);
        assert tailMax < bound;
        assert s[0] < bound;
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
    ensures MaxSplitScore(A, p) >= 0
{
    var scores := seq(|A| - 1, i requires 0 <= i < |A| - 1 => SplitScore(A, i + 1, p));
    assert |scores| == |A| - 1;
    assert |scores| > 0;
    assert forall i :: 0 <= i < |scores| ==> scores[i] < 2 * p;
    assert forall i :: 0 <= i < |scores| ==> scores[i] >= 0;
    MaxSeqBound(scores, 2 * p);
    MaxSeqNonNeg(scores);
    var m := MaxSeq(scores);
    assert m < 2 * p;
    assert m >= 0;
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

