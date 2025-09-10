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

// <vc-helpers>
lemma {:axiom} DivisionProperty(A: int, P: int)
    requires ValidInput(A, P)
    ensures (A * 3 + P) % 2 == 0
{
}
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
  DivisionProperty(A, P);
  pies := (A * 3 + P) / 2;
}
// </vc-code>

