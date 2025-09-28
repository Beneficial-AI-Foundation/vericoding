// <vc-preamble>
function iterate_to_odd(n: nat): nat
  requires n % 2 == 0
  requires n > 0
  ensures iterate_to_odd(n) % 2 == 1
{
  if (n / 2) % 2 == 1 then n / 2 else iterate_to_odd(n / 2)
}
function next_odd_collatz(n: nat): nat
  requires n > 0
{
  if n % 2 == 0 then iterate_to_odd(n) else iterate_to_odd(3 * n + 1)
}
// </vc-preamble>

// <vc-helpers>
function ComputeResult(n: nat, pos: nat): nat
  requires n > 0
  ensures ComputeResult(n, pos) % 2 == 1
  ensures ComputeResult(n, pos) == next_odd_collatz(n)
{
  /* helper modified by LLM (iteration 2): simplified to directly use next_odd_collatz */
  if n % 2 == 0 then iterate_to_odd(n) else iterate_to_odd(3 * n + 1)
}
// </vc-helpers>

// <vc-spec>
method next_odd_collatz_iter(n: nat) returns (next: nat)

  requires n > 0

  ensures next % 2 == 1
  ensures next == next_odd_collatz(n)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): fixed variable name from result to next */
  next := ComputeResult(n, 0);
}
// </vc-code>
