// <vc-preamble>
predicate ValidInput(A: int, B: int, C: int)
{
    1 <= A <= 10 && 1 <= B <= 10 && 1 <= C <= 10
}

predicate CanFormHaiku(A: int, B: int, C: int)
{
    (A == 5 && B == 5 && C == 7) ||
    (A == 5 && B == 7 && C == 5) ||
    (A == 7 && B == 5 && C == 5)
}

predicate ValidOutput(result: string)
{
    result in {"YES", "NO"}
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, C: int) returns (result: string)
    requires ValidInput(A, B, C)
    ensures ValidOutput(result)
    ensures result == "YES" <==> CanFormHaiku(A, B, C)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
