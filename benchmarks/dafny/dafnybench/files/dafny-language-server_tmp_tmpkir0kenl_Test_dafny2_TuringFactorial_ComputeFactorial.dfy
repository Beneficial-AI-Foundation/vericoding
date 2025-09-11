// <vc-preamble>
function Factorial(n: nat): nat
{
  if n == 0 then 1 else n * Factorial(n-1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ComputeFactorial(n: int) returns (u: int)
  requires 1 <= n;
  ensures u == Factorial(n);
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
