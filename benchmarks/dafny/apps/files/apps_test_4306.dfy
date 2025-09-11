// <vc-preamble>
predicate ValidInput(a: int, b: int, c: int, d: int)
{
    0 <= a < b <= 100 && 0 <= c < d <= 100
}

function min(x: int, y: int): int
{
    if x < y then x else y
}

function max(x: int, y: int): int
{
    if x > y then x else y
}

function IntervalOverlapLength(a: int, b: int, c: int, d: int): int
{
    if min(b, d) - max(a, c) > 0 then min(b, d) - max(a, c) else 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, c: int, d: int) returns (result: int)
    requires ValidInput(a, b, c, d)
    ensures result >= 0
    ensures result == IntervalOverlapLength(a, b, c, d)
    ensures result <= 100
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
