predicate ValidInput(a: int, b: int, c: int)
{
    1 <= a <= 1000 && 1 <= b <= 1000 && 1 <= c <= 1000
}

function MaxRecipeUnits(a: int, b: int, c: int): int
{
    min(a, min(b / 2, c / 4))
}

function TotalFruitsUsed(units: int): int
{
    units * 7
}

// <vc-helpers>
lemma MinNonNeg(x: int, y: int)
  requires x >= 0 && y >= 0
  ensures min(x, y) >= 0
{
  if x < y {
    assert min(x, y) == x;
  } else {
    assert min(x, y) == y;
  }
}

lemma MaxRecipeUnitsNonNeg(a: int, b: int, c: int)
  requires ValidInput(a, b, c)
  ensures MaxRecipeUnits(a, b, c) >= 0
{
  assert a >= 0;
  assert b / 2 >= 0;
  assert c / 4 >= 0;
  MinNonNeg(b / 2, c / 4);
  MinNonNeg(a, min(b / 2, c / 4));
  assert MaxRecipeUnits(a, b, c) == min(a, min(b / 2, c / 4));
  assert MaxRecipeUnits(a, b, c) >= 0;
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int) returns (result: int)
    requires ValidInput(a, b, c)
    ensures result == TotalFruitsUsed(MaxRecipeUnits(a, b, c))
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  result := TotalFruitsUsed(MaxRecipeUnits(a, b, c));
  MaxRecipeUnitsNonNeg(a, b, c);
}
// </vc-code>

