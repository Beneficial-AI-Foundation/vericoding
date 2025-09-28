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
lemma NextOddCollatzIsOdd(n: nat)
  requires n > 0
  ensures next_odd_collatz(n) % 2 == 1
{
  if n % 2 == 0 {
    assert n % 2 == 0;
    assert n > 0;
    assert next_odd_collatz(n) == iterate_to_odd(n);
    assert iterate_to_odd(n) % 2 == 1;
  } else {
    assert (3*n + 1) % 2 == 0;
    assert 3*n + 1 > 0;
    assert next_odd_collatz(n) == iterate_to_odd(3*n + 1);
    assert iterate_to_odd(3*n + 1) % 2 == 1;
  }
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
  next := next_odd_collatz(n);
  NextOddCollatzIsOdd(n);
  assert next == next_odd_collatz(n);
  assert next % 2 == 1;
}

// </vc-code>
