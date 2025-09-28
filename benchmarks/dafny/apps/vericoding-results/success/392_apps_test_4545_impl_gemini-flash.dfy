// <vc-preamble>
predicate ValidInput(N: int, A: int)
{
    1 <= N <= 100 && 0 <= A <= N * N
}

function BlackSquares(N: int, A: int): int
    requires ValidInput(N, A)
{
    N * N - A
}

predicate ValidOutput(N: int, A: int, result: int)
    requires ValidInput(N, A)
{
    result == BlackSquares(N, A) && result >= 0
}
// </vc-preamble>

// <vc-helpers>
function ComputeBlackSquares(N: int, A: int): int
    requires ValidInput(N, A)
    ensures ComputeBlackSquares(N, A) == N * N - A
{
    N * N - A
}
// </vc-helpers>

// <vc-spec>
method CalculateBlackSquares(N: int, A: int) returns (blackSquares: int)
    requires ValidInput(N, A)
    ensures ValidOutput(N, A, blackSquares)
// </vc-spec>
// <vc-code>
{
  blackSquares := ComputeBlackSquares(N, A);
}
// </vc-code>
