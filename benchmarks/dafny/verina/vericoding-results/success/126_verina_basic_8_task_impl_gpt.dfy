// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): define pure min function without 'method' keyword to satisfy function-syntax */
function min(a: int, b: int): int {
  if a <= b then a else b
}
// </vc-helpers>

// <vc-spec>
method MyMin(a: int, b: int) returns (result: int)
    ensures result <= a && result <= b
    ensures result == a || result == b
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): compute minimum using helper function */
  result := min(a, b);
}
// </vc-code>
