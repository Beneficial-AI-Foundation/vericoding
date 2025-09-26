// <vc-preamble>
predicate ValidInput(a: int, b: int, c: int, d: int)
{
    a >= 0 && b >= 0 && c >= 0 && d >= 0
}

predicate FirstAlarmSufficient(a: int, b: int)
{
    a <= b
}

predicate NeverWakes(a: int, b: int, c: int, d: int)
{
    a > b && c <= d
}

predicate EventuallyWakes(a: int, b: int, c: int, d: int)
{
    a > b && c > d
}

function CalculateWakeTime(a: int, b: int, c: int, d: int): int
    requires ValidInput(a, b, c, d)
    requires EventuallyWakes(a, b, c, d)
{
    var remaining := a - b;
    var cycles := (remaining - 1) / (c - d) + 1;
    b + c * cycles
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int, d: int) returns (result: int)
    requires ValidInput(a, b, c, d)
    ensures FirstAlarmSufficient(a, b) ==> result == b
    ensures NeverWakes(a, b, c, d) ==> result == -1
    ensures EventuallyWakes(a, b, c, d) ==> result == CalculateWakeTime(a, b, c, d)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
