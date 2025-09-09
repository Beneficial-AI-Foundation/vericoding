Given a sequence A of N integers and a positive integer p, split A into exactly 2 contiguous,
non-overlapping parts (each containing at least 1 element) to maximize the sum of their scores.
The score of a part is the sum of its elements modulo p. Find the maximum possible sum of scores.

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

function SumRange(A: seq<int>, start: int, end: int): int
    requires 0 <= start <= end <= |A|
    decreases end - start
{
    if start == end then 0
    else A[start] + SumRange(A, start + 1, end)
}

function SplitScore(A: seq<int>, splitPoint: int, p: int): int
    requires 1 <= splitPoint < |A|
    requires p >= 2
{
    var leftSum := SumRange(A, 0, splitPoint);
    var rightSum := SumRange(A, splitPoint, |A|);
    (leftSum % p) + (rightSum % p)
}

function MaxSeq(s: seq<int>): int
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else if s[0] >= MaxSeq(s[1..]) then s[0]
    else MaxSeq(s[1..])
}

method solve(N: int, p: int, A: seq<int>) returns (result: int)
    requires ValidInput(N, p, A)
    ensures result >= 0
    ensures result < 2 * p
    ensures result == MaxSplitScore(A, p)
{
    var leftSum := SumRange(A, 0, 1);
    var rightSum := SumRange(A, 1, N);
    var ans := (leftSum % p) + (rightSum % p);
    var i := 2;

    while i < N
        invariant 2 <= i <= N
        invariant ans >= 0
        invariant ans < 2 * p
        invariant ans == MaxSeq(seq(i - 1, j requires 0 <= j < i - 1 => SplitScore(A, j + 1, p)))
    {
        leftSum := SumRange(A, 0, i);
        rightSum := SumRange(A, i, N);
        var score := (leftSum % p) + (rightSum % p);

        assert score >= 0;
        assert leftSum % p >= 0 && leftSum % p < p;
        assert rightSum % p >= 0 && rightSum % p < p;
        assert score < 2 * p;

        if score > ans {
            ans := score;
        }

        assert ans == MaxSeq(seq(i, j requires 0 <= j < i => SplitScore(A, j + 1, p)));
        i := i + 1;
    }

    result := ans;
}
