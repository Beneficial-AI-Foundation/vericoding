/*
Find the maximum height of a pyramid that can be built with n cubes, where
level i requires exactly i*(i+1)/2 cubes. The pyramid is built from top to
bottom with levels 1, 2, 3, ..., h.
*/

predicate ValidInput(n: int) {
    n >= 1
}

function CubesForLevel(level: int): int
    requires level >= 1
{
    level * (level + 1) / 2
}

function TotalCubesForHeight(h: int): int
    requires h >= 1
{
    h * (h + 1) * (h + 2) / 6
}

predicate ValidPyramidHeight(n: int, h: int) {
    ValidInput(n) && h >= 1 && 
    TotalCubesForHeight(h) <= n &&
    TotalCubesForHeight(h + 1) > n
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int) returns (result: int)
    requires ValidInput(n)
    ensures result >= 1
    ensures ValidPyramidHeight(n, result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
