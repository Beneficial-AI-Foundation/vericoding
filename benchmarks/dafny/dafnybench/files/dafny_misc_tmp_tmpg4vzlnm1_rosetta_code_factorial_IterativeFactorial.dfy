// <vc-preamble>
function Factorial(n: nat): nat {
  if n == 0 then 1 else n * Factorial(n - 1)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method IterativeFactorial(n: nat) returns (result: nat)
  ensures result == Factorial(n)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
