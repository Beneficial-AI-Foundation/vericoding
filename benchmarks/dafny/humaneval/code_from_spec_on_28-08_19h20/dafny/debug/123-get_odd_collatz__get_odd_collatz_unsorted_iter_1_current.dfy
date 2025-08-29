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
method next_odd_collatz_iter(n: nat) returns (next: nat)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures next % 2 == 1
  ensures next == next_odd_collatz(n)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma next_odd_collatz_decreases(n: nat)
  requires n > 1
  ensures next_odd_collatz(n) < n
{
  if n % 2 == 0 {
    assert next_odd_collatz(n) == iterate_to_odd(n);
    iterate_to_odd_decreases(n);
  } else {
    assert next_odd_collatz(n) == iterate_to_odd(3 * n + 1);
    iterate_to_odd_decreases(3 * n + 1);
  }
}

lemma iterate_to_odd_decreases(n: nat)
  requires n % 2 == 0
  requires n > 0
  ensures iterate_to_odd(n) < n
{
  if (n / 2) % 2 == 1 {
    assert iterate_to_odd(n) == n / 2;
    assert n / 2 < n;
  } else {
    assert iterate_to_odd(n) == iterate_to_odd(n / 2);
    iterate_to_odd_decreases(n / 2);
    assert iterate_to_odd(n / 2) < n / 2 < n;
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method get_odd_collatz_unsorted(n: nat) returns (odd_collatz: seq<nat>)
Sort elements. Requires: requires n > 1. Ensures: the condition holds for all values; the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method get_odd_collatz_unsorted(n: nat) returns (odd_collatz: seq<nat>)
  decreases *
  requires n > 1
  ensures forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] % 2 == 1
  ensures forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] > 0
// </vc-spec>
// <vc-code>
method get_odd_collatz_unsorted(n: nat) returns (odd_collatz: seq<nat>)
  decreases *
  requires n > 1
  ensures forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] % 2 == 1
  ensures forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] > 0
{
  odd_collatz := [];
  var current := n;
  
  while current != 1
    invariant current > 0
    invariant forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] % 2 == 1
    invariant forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] > 0
    decreases *
  {
    if current % 2 == 1 {
      odd_collatz := odd_collatz + [current];
    }
    current := next_odd_collatz_iter(current);
  }
  
  odd_collatz := odd_collatz + [1];
}
// </vc-code>

method get_odd_collatz(n: nat) returns (sorted: seq<int>)
  decreases *
  requires n > 1
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i :: 0 <= i < |sorted| ==> sorted[i] % 2 == 1
{
  assume{:axiom} false;
}