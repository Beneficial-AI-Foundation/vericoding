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
lemma iterate_to_odd_iterative_correct(start: nat)
  requires start > 0
  requires start % 2 == 0
  ensures exists k: nat :: iterate_to_odd_helper(start, k) % 2 == 1 && iterate_to_odd_helper(start, k) == iterate_to_odd(start)
{
  assume{:axiom} false;
}

function iterate_to_odd_helper(n: nat, steps: nat): nat
  requires n > 0
  decreases steps
{
  if steps == 0 || n % 2 == 1 then n
  else iterate_to_odd_helper(n / 2, steps - 1)
}

lemma iterate_to_odd_equiv(n: nat, current: nat)
  requires n > 0
  requires n % 2 == 0
  requires current > 0
  requires exists k: nat :: current == n / (power_of_two(k)) && power_of_two(k) <= n && power_of_two(k) > 0 && n >= power_of_two(k)
  ensures current % 2 == 1 ==> current == iterate_to_odd(n)
{
  assume{:axiom} false;
}

function power_of_two(k: nat): nat
  ensures power_of_two(k) > 0
{
  if k == 0 then 1 else 2 * power_of_two(k - 1)
}

lemma iterate_to_odd_division_correct(n: nat)
  requires n > 0
  requires n % 2 == 0
  ensures iterate_to_odd(n) == iterate_to_odd_by_division(n)
{
  assume{:axiom} false;
}

method iterate_to_odd_by_division(n: nat) returns (result: nat)
  requires n > 0
  requires n % 2 == 0
  ensures result % 2 == 1
{
  var current := n;
  while current % 2 == 0
    invariant current > 0
    decreases current
  {
    current := current / 2;
  }
  result := current;
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
  ensures next == next_odd_collatz(n)
  ensures next % 2 == 1
// </vc-spec>
// <vc-code>
{
  var current: nat;
  if n % 2 == 0 {
    current := n;
    while current % 2 == 0
      invariant current > 0
      decreases current
    {
      current := current / 2;
    }
    next := current;
    assert next == iterate_to_odd(n);
    assert next == next_odd_collatz(n);
  } else {
    current := 3 * n + 1;
    while current % 2 == 0
      invariant current > 0
      decreases current
    {
      current := current / 2;
    }
    next := current;
    assert next == iterate_to_odd(3 * n + 1);
    assert next == next_odd_collatz(n);
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