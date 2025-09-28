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

// </vc-helpers>

// <vc-spec>
method next_odd_collatz_iter(n: nat) returns (next: nat)

  requires n > 0

  ensures next % 2 == 1
  ensures next == next_odd_collatz(n)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): fixed invariant to only call iterate_to_odd when current is even */
  var current := n;
  
  if current % 2 == 1 {
    current := 3 * current + 1;
  }
  
  while current % 2 == 0
    invariant current > 0
    invariant current % 2 == 0 ==> iterate_to_odd(current) == next_odd_collatz(n)
    invariant current % 2 == 1 ==> current == next_odd_collatz(n)
    decreases current
  {
    current := current / 2;
  }
  
  next := current;
}
// </vc-code>
