// <vc-preamble>
predicate ValidInput(N: int, M: int)
{
    N >= 1 && M >= 1
}

function CountFaceDownCards(N: int, M: int): int
    requires ValidInput(N, M)
{
    if N == 1 && M == 1 then 1
    else if N == 1 then M - 2
    else if M == 1 then N - 2
    else (N - 2) * (M - 2)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(N: int, M: int) returns (result: int)
    requires ValidInput(N, M)
    ensures result == CountFaceDownCards(N, M)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
