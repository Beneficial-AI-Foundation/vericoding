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
function collatz_sequence(n: nat): seq<nat>
  requires n > 0
  decreases if n == 1 then 0 else if n % 2 == 0 then n / 2 else 3 * n + 1
{
  if n == 1 then [1]
  else if n % 2 == 0 then [n] + collatz_sequence(n / 2)
  else [n] + collatz_sequence(3 * n + 1)
}

function filter_odd(s: seq<nat>): seq<nat>
{
  if |s| == 0 then []
  else if s[0] % 2 == 1 then [s[0]] + filter_odd(s[1..])
  else filter_odd(s[1..])
}

method compute_odd_collatz(n: nat) returns (odds: seq<nat>)
  requires n > 0
  ensures forall i :: 0 <= i < |odds| ==> odds[i] % 2 == 1
  ensures odds == filter_odd(collatz_sequence(n))
{
  var seq_full := collatz_sequence(n);
  odds := filter_odd(seq_full);
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
  requires n > 1
  ensures forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] % 2 == 1
  ensures odd_collatz == filter_odd(collatz_sequence(n))
// </vc-spec>
// <vc-code>
{
  odd_collatz := compute_odd_collatz(n);
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