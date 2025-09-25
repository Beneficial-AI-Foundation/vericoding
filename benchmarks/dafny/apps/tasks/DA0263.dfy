// <vc-preamble>
predicate ValidInput(a: int, b: int)
{
    0 <= a <= 100 && 0 <= b <= 100
}

predicate ValidOutput(result: string)
{
    result == "YES" || result == "NO"
}

predicate IntervalExists(a: int, b: int)
{
    abs(a - b) <= 1 && a + b > 0
}

function abs(x: int): int
{
    if x >= 0 then x else -x
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: string)
    requires ValidInput(a, b)
    ensures ValidOutput(result)
    ensures result == "YES" <==> IntervalExists(a, b)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
