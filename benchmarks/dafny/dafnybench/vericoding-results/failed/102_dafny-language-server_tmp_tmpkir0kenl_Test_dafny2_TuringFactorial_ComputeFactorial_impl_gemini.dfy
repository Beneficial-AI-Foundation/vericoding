// <vc-preamble>
function Factorial(n: nat): nat
{
  if n == 0 then 1 else n * Factorial(n-1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers are needed for an iterative solution. */
// </vc-helpers>

// <vc-spec>
method ComputeFactorial(n: int) returns (u: int)
  requires 1 <= n;
  ensures u == Factorial(n);
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Replaced the while loop with a cleaner for loop. */
{
  u := 1;
  for i := 2 to n 
    invariant u == Factorial(i - 1)
  {
    u := u * i;
  }
}
// </vc-code>
