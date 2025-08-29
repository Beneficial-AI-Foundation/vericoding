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
    assert iterate_to_odd(n / 2) < n / 2;
    assert n / 2 < n;
  }
}

lemma next_odd_collatz_positive(n: nat)
  requires n > 0
  ensures next_odd_collatz(n) > 0
{
  if n % 2 == 0 {
    assert next_odd_collatz(n) == iterate_to_odd(n);
  } else {
    assert next_odd_collatz(n) == iterate_to_odd(3 * n + 1);
    assert 3 * n + 1 > 0;
    assert (3 * n + 1) % 2 == 0;
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
  ensures forall i :: 1 <= i < |odd_collatz| ==> odd_collatz[i] == next_odd_collatz(odd_collatz[i - 1])
// </vc-spec>

// <vc-code>
{
  var current := n;
  odd_collatz := [];
  
  if current % 2 == 1 {
    odd_collatz := [current];
    current := next_odd_collatz(current);
    next_odd_collatz_positive(odd_collatz[0]);
  } else {
    current := next_odd_collatz(current);
    next_odd_collatz_positive(n);
  }
  
  odd_collatz := odd_collatz + [current];
  
  while current != 1
    invariant |odd_collatz| >= 1
    invariant forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] % 2 == 1
    invariant forall i :: 1 <= i < |odd_collatz| ==> odd_collatz[i] == next_odd_collatz(odd_collatz[i - 1])
    invariant current == odd_collatz[|odd_collatz| - 1]
    invariant current > 0
    decreases *
  {
    var next_val := next_odd_collatz(current);
    next_odd_collatz_positive(current);
    odd_collatz := odd_collatz + [next_val];
    current := next_val;
  }
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