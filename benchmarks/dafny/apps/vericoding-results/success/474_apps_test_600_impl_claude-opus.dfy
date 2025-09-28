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
function abs(x: int): int
{
    if x >= 0 then x else -x
}

function tirednessForSteps(n: int): int
    requires n >= 0
{
    n * (n + 1) / 2
}

lemma TirednessNonNegative(n: int)
    requires n >= 0
    ensures tirednessForSteps(n) >= 0
{
    // Dafny can prove this automatically
}

lemma OptimalMeetingPointProperties(a: int, b: int)
    requires ValidInput(a, b)
    ensures a <= b ==> a <= OptimalMeetingPoint(a, b) <= b
    ensures b <= a ==> b <= OptimalMeetingPoint(a, b) <= a
{
    // Dafny can prove this automatically
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
    var dist_a := abs(c - a);
    var dist_b := abs(b - c);
    
    TirednessNonNegative(dist_a);
    TirednessNonNegative(dist_b);
    
    var tiredness_a := tirednessForSteps(dist_a);
    var tiredness_b := tirednessForSteps(dist_b);
    
    result := tiredness_a + tiredness_b;
}
// </vc-code>

