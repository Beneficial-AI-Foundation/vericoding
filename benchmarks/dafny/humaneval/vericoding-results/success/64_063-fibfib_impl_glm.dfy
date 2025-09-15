// <vc-preamble>
function fibfib(n: nat): nat
  decreases n
{
  if n == 0 || n == 1 then 0
  else if n == 2 then 1
  else fibfib(n - 1) + fibfib(n - 2) + fibfib(n - 3)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ComputeFibFib(n: nat) returns (result: nat)

  ensures result == fibfib(n)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): use existing fibfib function to compute result */
  result := fibfib(n);
}
// </vc-code>
