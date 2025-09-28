// <vc-preamble>
predicate ValidInput(n: int, a: int)
{
    1 <= n <= 10000 && 0 <= a <= 1000
}

predicate CanPayExactly(n: int, a: int)
{
    n % 500 <= a
}

predicate ValidOutput(result: string)
{
    result == "Yes" || result == "No"
}
// </vc-preamble>

// <vc-helpers>
// No additional helpers needed for this problem
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int) returns (result: string)
    requires ValidInput(n, a)
    ensures ValidOutput(result)
    ensures result == "Yes" <==> CanPayExactly(n, a)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Initial implementation based on the problem description */
{
  if n % 500 <= a {
    result := "Yes";
  } else {
    result := "No";
  }
}
// </vc-code>
