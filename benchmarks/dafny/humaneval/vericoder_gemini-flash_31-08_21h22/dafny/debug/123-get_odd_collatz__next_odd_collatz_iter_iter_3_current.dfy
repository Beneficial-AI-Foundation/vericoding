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
// We need to rename the helper functions to avoid duplicate names with the preamble.
// The preamble functions are not used for verification, so these definitions
// will be the ones that are used.

function iter_to_odd(n: nat): nat
  requires n % 2 == 0
  requires n > 0
  ensures iter_to_odd(n) % 2 == 1
  ensures iter_to_odd(n) == if (n / 2) % 2 == 1 then n / 2 else iter_to_odd(n / 2)
{
  if (n / 2) % 2 == 1 then n / 2 else iter_to_odd(n / 2)
}

function next_odd_collatz(n: nat): nat
  requires n > 0
  ensures next_odd_collatz(n) % 2 == 1
  ensures next_odd_collatz(n) == (if n % 2 == 0 then iter_to_odd(n) else iter_to_odd(3 * n + 1))
{
  if n % 2 == 0 then iter_to_odd(n) else iter_to_odd(3 * n + 1)
}
// </vc-helpers>

// <vc-spec>
method next_odd_collatz_iter(n: nat) returns (next: nat)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures next % 2 == 1
  ensures next == next_odd_collatz(n)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var current_n := n;
  if current_n % 2 == 0 {
    while current_n % 2 == 0
      invariant current_n > 0
      invariant iter_to_odd(n) == iter_to_odd(current_n)
      decreases current_n
    {
      current_n := current_n / 2;
    }
  } else {
    current_n := 3 * current_n + 1;
    // The previous invariant `iterate_to_odd(3 * n + 1) == iterate_to_odd(current_n)`
    // was not correct considering the first part of the loop where `current_n` has
    // already been updated. We need to be careful with the loop invariant.
    // The `current_n` will become odd by repeatedly dividing by 2.
    while current_n % 2 == 0
      invariant current_n > 0
      invariant iter_to_odd(3 * n + 1) == iter_to_odd(current_n) // This invariant refers to the initial 3*n+1 which is what we need.
      decreases current_n
    {
      current_n := current_n / 2;
    }
  }
  next := current_n;
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