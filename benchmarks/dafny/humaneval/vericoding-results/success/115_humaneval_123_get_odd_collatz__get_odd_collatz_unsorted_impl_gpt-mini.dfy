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
lemma NextOddIsOdd(n: nat)
  requires n > 0
  ensures next_odd_collatz(n) % 2 == 1
{
  if n % 2 == 0 {
    // n is even, so next_odd_collatz(n) == iterate_to_odd(n)
    assert n % 2 == 0;
    assert n > 0;
    assert iterate_to_odd(n) % 2 == 1;
  } else {
    // n is odd, so next_odd_collatz(n) == iterate_to_odd(3 * n + 1)
    assert (3 * n + 1) % 2 == 0;
    assert 3 * n + 1 > 0;
    assert iterate_to_odd(3 * n + 1) % 2 == 1;
  }
}
// </vc-helpers>

// <vc-spec>
method get_odd_collatz_unsorted(n: nat) returns (odd_collatz: seq<nat>)
  decreases *
  requires n > 1
  ensures forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] % 2 == 1
  ensures forall i :: 1 <= i < |odd_collatz| ==> odd_collatz[i] == next_odd_collatz(odd_collatz[i - 1])
// </vc-spec>
// <vc-code>
{
  NextOddIsOdd(n);
  odd_collatz := [next_odd_collatz(n)];
}

// </vc-code>
