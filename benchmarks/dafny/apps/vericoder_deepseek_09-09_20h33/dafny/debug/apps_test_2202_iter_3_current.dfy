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
    requires p >= 2
    requires 1 <= k < |A|
{
    var left := A[0..k];
    var right := A[k..|A|];
    var left_sum := SumSeq(left);
    var right_sum := SumSeq(right);
    (left_sum - right_sum) % p
}

function SumSeq(s: seq<int>): int
    decreases s
{
    if |s| == 0 then 0
    else s[0] + SumSeq(s[1..])
}

function MaxSeq(s: seq<int>): int
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> s[i] <= result
    ensures exists i :: 0 <= i < |s| && s[i] == result
{
    if |s| == 1 then
        s[0]
    else
        var max_rest := MaxSeq(s[1..]);
        if s[0] > max_rest then s[0] else max_rest
}

lemma MaxSeqContains(s: seq<int>)
    requires |s| > 0
    ensures exists i :: 0 <= i < |s| && s[i] == MaxSeq(s)
{
}

lemma MaxSeqGeAll(s: seq<int>)
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> s[i] <= MaxSeq(s)
{
}

lemma ModRange(x: int, p: int)
    requires p >= 2
    ensures 0 <= x % p < p
    ensures 0 <= (x + p) % (2 * p) < 2 * p
{
}

lemma SplitScoreRange(A: seq<int>, k: int, p: int)
    requires |A| >= 2
    requires p >= 2
    requires 1 <= k < |A|
    ensures -p < SplitScore(A, k, p) < p
{
}

lemma MaxSplitScoreProperty(A: seq<int>, p: int)
    requires |A| >= 2
    requires p >= 2
    ensures -p < MaxSplitScore(A, p) < p
{
    var scores := seq(|A| - 1, i requires 0 <= i < |A| - 1 => SplitScore(A, i + 1, p));
    assert |scores| > 0;
    MaxSeqGeAll(scores);
    MaxSeqContains(scores);
    SplitScoreRange(A, 1, p);
}
// </vc-helpers>
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
    var scores := seq(|A| - 1, i requires 0 <= i < |A| - 1 => SplitScore(A, i + 1, p));
    var max_score := MaxSeq(scores);
    
    // Since SplitScore returns values in (-p, p), MaxSplitScore is also in (-p, p)
    assert forall i :: 0 <= i < |scores| ==> -p < scores[i] < p;
    assert -p < max_score < p;
    
    // Convert negative scores to positive modulo (2*p)
    if max_score < 0 {
        result := max_score + 2 * p;
    } else {
        result := max_score;
    }
    
    // Verify the result is in range and equals MaxSplitScore mod (2*p)
    assert 0 <= result < 2 * p;
    assert result == max_score % (2 * p); // mod for negative numbers
    assert max_score == MaxSplitScore(A, p);
}
// </vc-code>

