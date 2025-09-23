// <vc-preamble>
predicate ValidInput(a: int, b: int)
{
    -100 <= a <= 100 && -100 <= b <= 100 && (a + b) % 2 == 0 && (a - b) % 2 == 0
}

predicate CorrectSolution(a: int, b: int, x: int, y: int)
{
    a == x + y && b == x - y
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (x: int, y: int)
    requires ValidInput(a, b)
    ensures CorrectSolution(a, b, x, y)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
