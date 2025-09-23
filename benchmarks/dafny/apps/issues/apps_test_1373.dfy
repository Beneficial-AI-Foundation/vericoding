// <vc-preamble>
function ComputeSum(N: int, start: int): int
    requires start >= 0
    requires N >= 0
    decreases N + 1 - start
{
    if start > N + 1 then 0
    else start * (N - start + 1) + 1 + ComputeSum(N, start + 1)
}

predicate ValidInput(N: int, K: int)
{
    1 <= N <= 200000 && 1 <= K <= N + 1
}

predicate ValidOutput(result: int)
{
    result >= 0 && result < 1000000007
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(N: int, K: int) returns (result: int)
    requires ValidInput(N, K)
    ensures ValidOutput(result)
    ensures result == ComputeSum(N, K) % 1000000007
// </vc-spec>
// <vc-code>
{
    var s := 0;
    var i := K;
    while i <= N + 1
        decreases N + 1 - i
        invariant K <= i <= N + 2
        invariant s >= 0
        invariant s == ComputeSum(N, K) - ComputeSum(N, i)
    {
        s := s + i * (N - i + 1) + 1;
        i := i + 1;
    }
    result := s % 1000000007;
}
// </vc-code>
