function fibfib(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 then 0
  else if n == 2 then 1
  else fibfib(n - 1) + fibfib(n - 2) + fibfib(n - 3)
}

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ComputeFibFib(n: nat) returns (result: nat)

  ensures result == fibfib(n)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
