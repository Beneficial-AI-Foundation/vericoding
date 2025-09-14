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
function Max(a: int, b: int): int
{
    if a >= b then a else b
}

function SplitScore(A: seq<int>, k: int, p: int): int
    requires 1 <= k < |A|
    requires p >= 2
    ensures 0 <= SplitScore(A, k, p) < p
{
    var first := A[0..k];
    var second := A[k..];
    var maxFirst := MaxSeq(first);
    var maxSecond := MaxSeq(second);
    if maxFirst == maxSecond then
        (maxFirst + maxSecond) % p
    else
        (maxFirst + maxSecond + 1) % p
}

function MaxSeq(s: seq<int>): int
    requires |s| > 0
    ensures forall i :: 0 <= i < |s| ==> s[i] <= MaxSeq(s)
    ensures exists i :: 0 <= i < |s| && MaxSeq(s) == s[i]
{
    if |s| == 1 then s[0] else Max(s[0], MaxSeq(s[1..]))
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
    return MaxSplitScore(A, p);
}
// </vc-code>

