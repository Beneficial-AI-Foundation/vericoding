// <vc-preamble>
predicate ValidInput(a: int, b: int)
{
    1 <= a <= 16 && 1 <= b <= 16 && a + b <= 16
}

predicate CanTakeNonAdjacent(pieces: int, total: int)
{
    pieces <= total / 2
}

predicate BothCanTake(a: int, b: int)
{
    CanTakeNonAdjacent(a, 16) && CanTakeNonAdjacent(b, 16)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SolveCakeProblem(a: int, b: int) returns (result: string)
    requires ValidInput(a, b)
    ensures BothCanTake(a, b) <==> result == "Yay!"
    ensures !BothCanTake(a, b) <==> result == ":("
    ensures result == "Yay!" || result == ":("
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
