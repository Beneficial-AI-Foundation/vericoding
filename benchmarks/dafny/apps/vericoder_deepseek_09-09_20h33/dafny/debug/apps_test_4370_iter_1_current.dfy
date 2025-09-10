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
lemma lemma_CanTakeNonAdjacentCondition(a: int, b: int)
  requires ValidInput(a, b)
  ensures BothCanTake(a, b) <==> (a <= 8 && b <= 8)
{
  // BothCanTake(a, b) means both a and b are <= 16/2 = 8
  // Since total = 16, CanTakeNonAdjacent(x, 16) is equivalent to x <= 8
}

lemma lemma_CheckResult(a: int, b: int)
  requires ValidInput(a, b)
  ensures (a <= 8 && b <= 8) <==> BothCanTake(a, b)
{
  // This is essentially the same as the previous lemma, redundant but helps verification
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
  if a <= 8 && b <= 8 {
    result := "Yay!";
  } else {
    result := ":(";
  }
}
// </vc-code>

