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
lemma iterate_to_odd_decreases(n: nat)
  requires n % 2 == 0
  requires n > 0
  requires (n / 2) % 2 == 0
  ensures n / 2 < n
{
  assert n >= 2;
  assert n / 2 < n;
}

lemma iterate_to_odd_result_odd(n: nat)
  requires n % 2 == 0
  requires n > 0
  ensures iterate_to_odd(n) % 2 == 1
{
}

lemma three_n_plus_one_even(n: nat)
  requires n > 0
  requires n % 2 == 1
  ensures (3 * n + 1) % 2 == 0
{
  assert 3 * n % 2 == 1;
  assert (3 * n + 1) % 2 == 0;
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
  if n % 2 == 1 {
    var temp := 3 * n + 1;
    assert temp % 2 == 0 by {
      three_n_plus_one_even(n);
    }
    next := iterate_to_odd(temp);
  } else {
    next := iterate_to_odd(n);
  }
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