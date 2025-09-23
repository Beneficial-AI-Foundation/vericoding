// <vc-preamble>
predicate ValidInput(A: int, P: int)
{
    0 <= A <= 100 && 0 <= P <= 100
}

function TotalPieces(A: int, P: int): int
    requires ValidInput(A, P)
{
    A * 3 + P
}

function MaxPies(A: int, P: int): int
    requires ValidInput(A, P)
{
    TotalPieces(A, P) / 2
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CalculateMaxPies(A: int, P: int) returns (pies: int)
    requires ValidInput(A, P)
    ensures pies == MaxPies(A, P)
    ensures pies >= 0
    ensures pies == (A * 3 + P) / 2
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
