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

// <vc-helpers>
function iterate_to_odd_helper(n: nat): nat
  requires n > 0
  ensures iterate_to_odd_helper(n) % 2 == 1
  decreases n
{
  if n % 2 == 1 then n else iterate_to_odd_helper(n / 2)
}

function next_odd_collatz_func(n: nat): nat
  requires n > 0
  ensures next_odd_collatz_func(n) % 2 == 1
{
  if n % 2 == 0 then iterate_to_odd_helper(n) else iterate_to_odd_helper(3 * n + 1)
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method next_odd_collatz_iter(n: nat) returns (next: nat)
Process input. Requires: requires n > 0. Ensures: returns the correct value; returns the correct value.
*/
// </vc-description>

// <vc-spec>
method next_odd_collatz_iter(n: nat) returns (next: nat)
  requires n > 0
  ensures next == next_odd_collatz_func(n)
  ensures next % 2 == 1
// </vc-spec>
// <vc-code>
{
  var current := n;
  if current % 2 == 0 {
    while current % 2 == 0
      invariant current > 0
      invariant next_odd_collatz_func(n) == next_odd_collatz_func(current)
      decreases current
    {
      current := current / 2;
    }
  } else {
    current := 3 * current + 1;
    while current % 2 == 0
      invariant current > 0
      invariant next_odd_collatz_func(n) == next_odd_collatz_func(current)
      decreases current
    {
      current := current / 2;
    }
  }
  next := current;
}
// </vc-code>

method get_odd_collatz_unsorted(n: nat) returns (odd_collatz: seq<nat>)
  decreases *
  requires n > 1
  ensures forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] % 2 == 1
  ensures forall i :: 1 <= i < |odd_collatz| ==> odd_collatz[i] == next_odd_collatz(odd_collatz[i - 1])
{
  assume{:axiom} false;
}
method get_odd_collatz(n: nat) returns (sorted: seq<int>)
  decreases *
  requires n > 1
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i :: 0 <= i < |sorted| ==> sorted[i] % 2 == 1
{
  assume{:axiom} false;
}