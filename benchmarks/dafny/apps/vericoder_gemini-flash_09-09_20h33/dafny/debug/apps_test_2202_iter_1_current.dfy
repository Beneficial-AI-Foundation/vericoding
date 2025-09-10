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
    requires 0 < k < |A|
    requires p >= 2
    reads A
{
    var sum1 := 0;
    for i := 0 to k - 1 {
        sum1 := sum1 + A[i];
    }
    var sum2 := 0;
    for i := k to |A| - 1 {
        sum2 := sum2 + A[i];
    }
    (sum1 % p) + (sum2 % p)
}

function MaxSeq(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then
        s[0]
    else
        var max_of_rest := MaxSeq(s[1..]);
        if s[0] > max_of_rest then
            s[0]
        else
            max_of_rest
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
    var max_score := 0;
    for k := 1 to N - 1
        invariant 1 <= k <= N
        invariant max_score == MaxSeq(seq(k - 1, i requires 0 <= i < k - 1 => SplitScore(A, i + 1, p)))
    {
        var current_score := SplitScore(A, k, p);
        if current_score > max_score {
            max_score := current_score;
        }
    }
    result := max_score;
}
// </vc-code>

