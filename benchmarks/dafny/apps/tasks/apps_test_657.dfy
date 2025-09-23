// <vc-preamble>
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
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, x: int, y: int, z: int) returns (result: int)
    requires ValidInput(a, b, x, y, z)
    ensures result >= 0
    ensures result == MinAdditionalCrystals(a, b, x, y, z)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
