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
lemma MaxZeroLemma(value: int)
    ensures max(0, value) == (if value <= 0 then 0 else value)
{
}

lemma YellowCrystalsSubtractLemma(a: int, x: int, y: int)
    requires a >= 0 && x >= 0 && y >= 0
    ensures max(0, YellowCrystalsNeeded(x, y) - a) == (if YellowCrystalsNeeded(x, y) <= a then 0 else YellowCrystalsNeeded(x, y) - a)
{
}

lemma BlueCrystalsSubtractLemma(b: int, y: int, z: int)
    requires b >= 0 && y >= 0 && z >= 0
    ensures max(0, BlueCrystalsNeeded(y, z) - b) == (if BlueCrystalsNeeded(y, z) <= b then 0 else BlueCrystalsNeeded(y, z) - b)
{
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
  var yellowNeeded := x * 2 + y;
  var blueNeeded := y + z * 3;
  
  var yellowDeficit := if yellowNeeded <= a then 0 else yellowNeeded - a;
  var blueDeficit := if blueNeeded <= b then 0 else blueNeeded - b;
  
  result := yellowDeficit + blueDeficit;
}
// </vc-code>

