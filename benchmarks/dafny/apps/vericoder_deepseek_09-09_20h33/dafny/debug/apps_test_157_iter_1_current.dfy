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
lemma MaxRecipeUnitsLemma(a: int, b: int, c: int, units: int)
  requires ValidInput(a, b, c)
  requires units == min(a, min(b / 2, c / 4))
  requires a >= 0 && b >= 0 && c >= 0
  ensures units * 7 == TotalFruitsUsed(MaxRecipeUnits(a, b, c))
{
}

lemma NonNegativeUnits(a: int, b: int, c: int)
  requires ValidInput(a, b, c)
  ensures MaxRecipeUnits(a, b, c) >= 0
{
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
  var units := a;
  if (b / 2 < units) {
    units := b / 2;
  }
  if (c / 4 < units) {
    units := c / 4;
  }
  result := units * 7;
  
  MaxRecipeUnitsLemma(a, b, c, units);
}
// </vc-code>

