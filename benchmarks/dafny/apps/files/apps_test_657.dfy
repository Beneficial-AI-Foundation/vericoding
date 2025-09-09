Given initial counts of yellow and blue crystals, determine the minimum additional crystals needed to produce a specified number of colored balls.
Yellow ball requires 2 yellow crystals, green ball requires 1 yellow + 1 blue crystal, blue ball requires 3 blue crystals.

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

method solve(a: int, b: int, x: int, y: int, z: int) returns (result: int)
    requires ValidInput(a, b, x, y, z)
    ensures result >= 0
    ensures result == MinAdditionalCrystals(a, b, x, y, z)
{
    var yellowNeeded := YellowCrystalsNeeded(x, y);
    var blueNeeded := BlueCrystalsNeeded(y, z);
    var additionalYellow := max(yellowNeeded - a, 0);
    var additionalBlue := max(blueNeeded - b, 0);
    result := additionalYellow + additionalBlue;
}
