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
  requires n % 2 == 0 && n > 0
  ensures iterate_to_odd(n) < n || n == 2
{
  if n == 2 {
  } else if (n / 2) % 2 == 1 {
    assert n / 2 < n;
  } else {
    iterate_to_odd_decreases(n / 2);
  }
}

lemma iterate_to_odd_positive(n: nat)
  requires n % 2 == 0 && n > 0
  ensures iterate_to_odd(n) > 0
{
  if (n / 2) % 2 == 1 {
    // n/2 > 0 when n ≥ 2
  } else {
    iterate_to_odd_positive(n / 2);
  }
}

predicate is_finite_collatz(n: nat)
  requires n > 0
  decreases if n == 1 then 0 else 1
{
  n == 1 || is_finite_collatz(next_odd_collatz(n))
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
  var current := n;
  odd_collatz := [];
  while current != 1
    decreases *
    invariant current > 0
    invariant forall x :: x in odd_collatz ==> x % 2 == 1
    invariant |odd_collatz| > 0 ==> odd_collatz[|odd_collatz|-1] == next_odd_collatz(current)
  {
    if current % 2 == 1 {
      odd_collatz := odd_collatz + [current];
      current := next_odd_collatz(current);
    } else {
      current := next_odd_collatz(current);
    }
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