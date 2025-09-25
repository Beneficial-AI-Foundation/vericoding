// <vc-preamble>
predicate ValidFarmDimensions(a: int, b: int)
{
    a >= 2 && b >= 2 && a <= 100 && b <= 100
}

function RemainingFarmArea(a: int, b: int): int
    requires ValidFarmDimensions(a, b)
{
    a * b - a - b + 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: int)
    requires ValidFarmDimensions(a, b)
    ensures result == RemainingFarmArea(a, b)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
