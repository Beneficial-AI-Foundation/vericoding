// <vc-preamble>
predicate ValidInput(n: int, x: int, a: int, b: int)
{
    2 <= n <= 100 && 0 <= x <= 100 && 1 <= a <= n && 1 <= b <= n && a != b
}

function MaxDistance(n: int, x: int, a: int, b: int): int
    requires ValidInput(n, x, a, b)
{
    var initialDistance := if a >= b then a - b else b - a;
    var maxPossibleDistance := initialDistance + x;
    var maxLineDistance := n - 1;
    if maxPossibleDistance <= maxLineDistance then maxPossibleDistance else maxLineDistance
}

predicate ValidResult(n: int, x: int, a: int, b: int, result: int)
    requires ValidInput(n, x, a, b)
{
    result == MaxDistance(n, x, a, b) && 0 <= result <= n - 1
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SolveRivalDistance(n: int, x: int, a: int, b: int) returns (result: int)
    requires ValidInput(n, x, a, b)
    ensures ValidResult(n, x, a, b, result)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
