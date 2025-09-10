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
function tirednessForSteps(n: int): int
    requires n >= 0
{
    n * (n + 1) / 2
}

function abs(n: int): int
{
    if n < 0 then -n else n
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
    var steps_a := abs(c - a);
    var steps_b := abs(b - c);

    result := tirednessForSteps(steps_a) + tirednessForSteps(steps_b);
}
// </vc-code>

