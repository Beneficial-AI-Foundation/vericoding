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
/* helper modified by LLM (iteration 2): Removed comment to fix parsing issue. */
// </vc-helpers>

// <vc-spec>
method solve(A: int, B: int, C: int) returns (result: string)
    requires ValidInput(A, B, C)
    ensures ValidOutput(result)
    ensures result == "YES" <==> CanFormHaiku(A, B, C)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed syntax error by adding braces around the if-then-else body. */
{
  if CanFormHaiku(A, B, C) {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>
