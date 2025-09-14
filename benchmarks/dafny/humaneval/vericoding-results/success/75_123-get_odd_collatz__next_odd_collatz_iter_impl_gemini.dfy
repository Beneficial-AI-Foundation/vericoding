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
lemma lemma_3np1_is_even_and_positive(n: nat)
  requires n > 0 && n % 2 == 1
  ensures (3*n+1) > 0 && (3*n+1) % 2 == 0
{
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
  /* code modified by LLM (iteration 5): strengthened loop invariant to prove postcondition */
  var temp: nat;
  if n % 2 == 0 {
    temp := n;
  } else {
    lemma_3np1_is_even_and_positive(n);
    temp := 3 * n + 1;
  }

  assert temp > 0 && temp % 2 == 0;
  assert next_odd_collatz(n) == iterate_to_odd(temp); 

  while temp % 2 == 0
    invariant temp > 0
    invariant next_odd_collatz(n) == if temp % 2 == 0 then iterate_to_odd(temp) else temp
    decreases temp
  {
    temp := temp / 2;
  }

  next := temp;
}
// </vc-code>
