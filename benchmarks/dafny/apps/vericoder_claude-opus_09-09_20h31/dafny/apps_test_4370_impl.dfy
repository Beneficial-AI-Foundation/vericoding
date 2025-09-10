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

// <vc-helpers>
lemma BothCanTakeCondition(a: int, b: int)
    requires ValidInput(a, b)
    ensures BothCanTake(a, b) <==> (a <= 8 && b <= 8)
{
    assert 16 / 2 == 8;
    assert CanTakeNonAdjacent(a, 16) <==> a <= 8;
    assert CanTakeNonAdjacent(b, 16) <==> b <= 8;
}
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
    BothCanTakeCondition(a, b);
    
    if a <= 8 && b <= 8 {
        result := "Yay!";
    } else {
        result := ":(";
    }
}
// </vc-code>

