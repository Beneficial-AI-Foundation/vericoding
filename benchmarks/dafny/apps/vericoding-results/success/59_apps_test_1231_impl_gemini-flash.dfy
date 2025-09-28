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
/* helper modified by LLM (iteration 2): fixed helper replacement, original was empty */

// </vc-helpers>

// <vc-spec>
method solve(a: int, b: int) returns (result: string)
    requires ValidInput(a, b)
    ensures ValidOutput(result)
    ensures result == "YES" <==> IntervalExists(a, b)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed compilation errors by enclosing if-else in curly braces */
{
  if (abs(a - b) <= 1 && a + b > 0) {
    result := "YES";
  } else {
    result := "NO";
  }
}
// </vc-code>
