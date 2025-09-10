function max(a: int, b: int): int
{
    if a >= b then a else b
}

predicate ValidInput(a: int, b: int, x: int, y: int, z: int)
{
    a >= 0 && b >= 0 && x >= 0 && y >= 0 && z >= 0
}

function YellowCrystalsNeeded(x: int, y: int): int
{
    x * 2 + y
}

function BlueCrystalsNeeded(y: int, z: int): int
{
    y + z * 3
}

function MinAdditionalCrystals(a: int, b: int, x: int, y: int, z: int): int
{
    max(0, YellowCrystalsNeeded(x, y) - a) + max(0, BlueCrystalsNeeded(y, z) - b)
}

// <vc-helpers>
lemma MaxNonNegative(a: int, b: int)
  ensures max(a, b) >= a && max(a,b) >= b
{
}

lemma MinAdditionalCrystalsNonNegative(a: int, b: int, x: int, y: int, z: int)
  requires ValidInput(a, b, x, y, z)
  ensures MinAdditionalCrystals(a, b, x, y, z) >= 0
{
  assert YellowCrystalsNeeded(x, y) >= 0;
  assert BlueCrystalsNeeded(y, z) >= 0;
  MaxNonNegative(0, YellowCrystalsNeeded(x, y) - a);
  MaxNonNegative(0, BlueCrystalsNeeded(y, z) - b);
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, x: int, y: int, z: int) returns (result: int)
    requires ValidInput(a, b, x, y, z)
    ensures result >= 0
    ensures result == MinAdditionalCrystals(a, b, x, y, z)
// </vc-spec>
// <vc-code>
{
  var yellowNeeded := YellowCrystalsNeeded(x, y);
  var blueNeeded := BlueCrystalsNeeded(y, z);

  var yellowDeficit := max(0, yellowNeeded - a);
  var blueDeficit := max(0, blueNeeded - b);

  result := yellowDeficit + blueDeficit;

  MinAdditionalCrystalsNonNegative(a, b, x, y, z);
}
// </vc-code>

