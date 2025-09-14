predicate ValidFarmDimensions(a: int, b: int)
{
    a >= 2 && b >= 2 && a <= 100 && b <= 100
}

function RemainingFarmArea(a: int, b: int): int
    requires ValidFarmDimensions(a, b)
{
    a * b - a - b + 1
}

// <vc-helpers>
lemma NonNegativeRemainingFarmArea(a: int, b: int)
    requires ValidFarmDimensions(a, b)
    ensures RemainingFarmArea(a, b) >= 0
{
    calc {
        RemainingFarmArea(a, b);
        a * b - a - b + 1;
        (a-1)*(b-1);
    }
    assert (a-1)*(b-1) >= 1;
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: int)
    requires ValidFarmDimensions(a, b)
    ensures result == RemainingFarmArea(a, b)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    NonNegativeRemainingFarmArea(a, b);
    return RemainingFarmArea(a, b);
}
// </vc-code>

