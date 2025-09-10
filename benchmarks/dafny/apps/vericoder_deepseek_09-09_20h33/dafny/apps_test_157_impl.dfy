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
  requires units == if b/2 < c/4 then min(a, b/2) else min(a, c/4)
  requires a >= 0 && b >= 0 && c >= 0
  ensures units * 7 == TotalFruitsUsed(if b/2 < c/4 then min(a, b/2) else min(a, c/4))
{
}

lemma NonNegativeUnits(a: int, b: int, c: int)
  requires ValidInput(a, b, c)
  ensures (if b/2 < c/4 then min(a, b/2) else min(a, c/4)) >= 0
{
}

function min(x: int, y: int): int
{
  if x <= y then x else y
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
  var b_units := b / 2;
  var c_units := c / 4;
  
  var units := a;
  if (b_units < units) {
    units := b_units;
  }
  if (c_units < units) {
    units := c_units;
  }
  result := units * 7;
  
  MaxRecipeUnitsLemma(a, b, c, units);
}
// </vc-code>

