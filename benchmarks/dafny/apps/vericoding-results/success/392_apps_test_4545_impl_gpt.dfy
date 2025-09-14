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

// <vc-helpers>
lemma BlackSquaresNonNeg(N: int, A: int)
  requires ValidInput(N, A)
  ensures BlackSquares(N, A) >= 0
{
}
// </vc-helpers>

// <vc-spec>
method CalculateBlackSquares(N: int, A: int) returns (blackSquares: int)
    requires ValidInput(N, A)
    ensures ValidOutput(N, A, blackSquares)
// </vc-spec>
// <vc-code>
{
  blackSquares := BlackSquares(N, A);
}
// </vc-code>

