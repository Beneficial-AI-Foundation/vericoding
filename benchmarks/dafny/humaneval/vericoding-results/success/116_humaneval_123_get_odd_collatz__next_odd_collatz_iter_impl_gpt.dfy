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
lemma odd3nPlus1Even(n: nat)
  requires n % 2 == 1
  ensures (3 * n + 1) % 2 == 0
{
  var k := n / 2;
  assert n == 2 * k + n % 2;
  assert n == 2 * k + 1;
  assert 3 * n + 1 == 3 * (2 * k + 1) + 1;
  assert 3 * (2 * k + 1) == 6 * k + 3;
  assert 3 * n + 1 == (6 * k + 3) + 1;
  assert 3 * n + 1 == 6 * k + 4;
  assert 6 * k + 4 == 2 * (3 * k + 2);
  assert 3 * n + 1 == 2 * (3 * k + 2);
  assert ((3 * n + 1) % 2) == ((2 * (3 * k + 2)) % 2);
  assert ((2 * (3 * k + 2)) % 2) == 0;
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
  if n % 2 == 0 {
    next := iterate_to_odd(n);
  } else {
    odd3nPlus1Even(n);
    next := iterate_to_odd(3 * n + 1);
  }
}
// </vc-code>
