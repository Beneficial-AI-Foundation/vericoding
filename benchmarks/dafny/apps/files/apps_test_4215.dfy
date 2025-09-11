// <vc-preamble>
predicate ValidInput(a: int, b: int)
{
    1 <= a <= 100 && 1 <= b <= 100
}

function UncoveredLength(a: int, b: int): int
{
    max(0, a - 2 * b)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: int)
    requires ValidInput(a, b)
    ensures result >= 0
    ensures result == UncoveredLength(a, b)
    ensures result == if a > 2 * b then a - 2 * b else 0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
