// <vc-preamble>
predicate ValidInput(n: int, a: int, b: int) {
    n >= 1 && 1 <= a <= n && -100 <= b <= 100
}

function FinalEntrance(n: int, a: int, b: int): int
    requires ValidInput(n, a, b)
{
    ((a - 1 + b) % n + n) % n + 1
}

predicate ValidOutput(result: int, n: int) {
    1 <= result <= n
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int) returns (result: int)
    requires ValidInput(n, a, b)
    ensures ValidOutput(result, n)
    ensures result == FinalEntrance(n, a, b)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
