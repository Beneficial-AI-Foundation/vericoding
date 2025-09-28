// <vc-preamble>
predicate ValidInput(a: int, b: int, x: int)
{
    1 <= a <= 100 && 1 <= b <= 100 && 1 <= x <= 200
}

predicate CanHaveExactlyCats(a: int, b: int, x: int)
{
    a <= x <= a + b
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed duplicate predicate definition. */
// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int, x: int) returns (result: string)
    requires ValidInput(a, b, x)
    ensures result == "YES" <==> CanHaveExactlyCats(a, b, x)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): No change as it verified correctly */
{
  if CanHaveExactlyCats(a, b, x) {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>
