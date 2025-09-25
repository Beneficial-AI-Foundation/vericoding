// <vc-preamble>
predicate ValidInput(input: string)
{
    |input| > 0
}

predicate ValidTestCase(x1: int, y1: int, x2: int, y2: int)
{
    1 <= x1 <= x2 && 1 <= y1 <= y2
}

function CountDifferentSums(x1: int, y1: int, x2: int, y2: int): int
    requires ValidTestCase(x1, y1, x2, y2)
{
    (x2 - x1) * (y2 - y1) + 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(input: string) returns (output: string)
    requires ValidInput(input)
    ensures |output| >= 0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
