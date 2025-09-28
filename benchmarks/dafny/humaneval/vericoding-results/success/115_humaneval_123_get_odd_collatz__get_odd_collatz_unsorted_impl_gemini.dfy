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
lemma iterate_to_odd_positive(n: nat)
  requires n > 0 && n % 2 == 0
  ensures iterate_to_odd(n) > 0
  decreases n
{
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
  var current: nat;
  if n % 2 == 0 {
    current := iterate_to_odd(n);
  } else {
    current := n;
  }
  
  odd_collatz := [];

  while current != 1
    decreases *
    invariant forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] % 2 == 1
    invariant forall i :: 1 <= i < |odd_collatz| ==> odd_collatz[i] == next_odd_collatz(odd_collatz[i-1])
    invariant current > 0 && current % 2 == 1
    invariant |odd_collatz| == 0 ==> current == (if n % 2 == 1 then n else iterate_to_odd(n))
    invariant |odd_collatz| > 0 ==> current == next_odd_collatz(odd_collatz[|odd_collatz|-1])
  {
    odd_collatz := odd_collatz + [current];
    current := next_odd_collatz(current);
  }

  odd_collatz := odd_collatz + [1];
}
// </vc-code>
