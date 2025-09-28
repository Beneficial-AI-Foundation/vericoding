// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): changed function method to function */
function max(x: int, y: int): int
  ensures max(x,y) >= x && max(x,y) >= y
  ensures max(x,y) == x || max(x,y) == y
{
  if x >= y then x else y
}
// </vc-helpers>

// <vc-spec>
method MaxOfThree(a: int, b: int, c: int) returns (result: int)
    ensures result >= a && result >= b && result >= c
    ensures result == a || result == b || result == c
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): using helper function to compute max */
  result := max(max(a, b), c);
}
// </vc-code>
