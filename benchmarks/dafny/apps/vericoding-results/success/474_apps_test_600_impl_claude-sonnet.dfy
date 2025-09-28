predicate ValidInput(a: int, b: int)
{
    a >= 1 && a <= 1000 && b >= 1 && b <= 1000 && a != b
}

function OptimalMeetingPoint(a: int, b: int): int
{
    (a + b) / 2
}

function MinimumTotalTiredness(a: int, b: int): int
    requires ValidInput(a, b)
{
    var c := OptimalMeetingPoint(a, b);
    tirednessForSteps(abs(c - a)) + tirednessForSteps(abs(b - c))
}

// <vc-helpers>
function tirednessForSteps(steps: int): int
    requires steps >= 0
{
    steps * steps
}

function abs(x: int): int
{
    if x >= 0 then x else -x
}
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: int)
    requires ValidInput(a, b)
    ensures result >= 0
    ensures result == MinimumTotalTiredness(a, b)
// </vc-spec>
// <vc-code>
{
    var c := OptimalMeetingPoint(a, b);
    var distance_a := abs(c - a);
    var distance_b := abs(b - c);
    result := tirednessForSteps(distance_a) + tirednessForSteps(distance_b);
}
// </vc-code>

