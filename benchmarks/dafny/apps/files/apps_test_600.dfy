Two friends at integer positions a and b on a number line need to meet at the same position.
Each move costs increasing tiredness: 1st move costs 1, 2nd move costs 2, etc.
Find the minimum total tiredness for both friends to meet.

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

function abs(x: int): int
{
    if x >= 0 then x else -x
}

function tirednessForSteps(steps: int): int
    requires steps >= 0
{
    steps * (steps + 1) / 2
}

method solve(a: int, b: int) returns (result: int)
    requires ValidInput(a, b)
    ensures result >= 0
    ensures result == MinimumTotalTiredness(a, b)
{
    var c := OptimalMeetingPoint(a, b);
    var cost1 := tirednessForSteps(abs(c - a));
    var cost2 := tirednessForSteps(abs(b - c));
    result := cost1 + cost2;
}
