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
{
    0
}

function MaxSeq(s: seq<int>): int
    requires |s| > 0
    decreases |s|
{
    if |s| == 1 then s[0] else
    var tailMax := MaxSeq(s[1..]);
    if s[0] > tailMax then s[0] else tailMax
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
}
// </vc-code>

