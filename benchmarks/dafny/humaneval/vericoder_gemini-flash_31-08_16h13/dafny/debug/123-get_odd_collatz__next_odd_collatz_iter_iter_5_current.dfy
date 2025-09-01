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
function iterate_to_odd_termination(n: nat): nat
  requires n > 0
{
  if n % 2 == 1 then n
  else if (n / 2) % 2 == 1 then n / 2
  else iterate_to_odd_termination(n / 2)
}

lemma lemma_iterate_to_odd_eq(n: nat)
  requires n > 0
  ensures iterate_to_odd_termination(n) == iterate_to_odd(n)
{
  if n % 2 == 1 {}
  else if (n / 2) % 2 == 1 {}
  else {
    lemma_iterate_to_odd_eq(n / 2);
  }
}

lemma lemma_iterate_to_odd_properties(n: nat)
  requires n > 0
  ensures iterate_to_odd(n) % 2 == 1
{
  if n % 2 == 0 {
    if (n / 2) % 2 == 1 {}
    else {
      lemma_iterate_to_odd_properties(n / 2);
    }
  }
}

lemma lemma_next_odd_collatz_properties(n: nat)
  requires n > 0
  ensures next_odd_collatz(n) % 2 == 1
{
  if n % 2 == 0 {
    lemma_iterate_to_odd_properties(n);
  } else {
    lemma_iterate_to_odd_properties(3 * n + 1);
  }
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
    if n % 2 == 0 {
      var current_n := n;
      while current_n % 2 == 0
        invariant current_n > 0
        invariant iterate_to_odd(current_n) == iterate_to_odd(n)
        invariant iterate_to_odd_termination(current_n) == iterate_to_odd_termination(n)
        decreases current_n
      {
        if (current_n / 2) % 2 == 1 {
          lemma_iterate_to_odd_eq(current_n);
          current_n := current_n / 2;
        } else {
          lemma_iterate_to_odd_eq(current_n);
          current_n := current_n / 2;
        }
      }
      next := current_n;
      lemma_iterate_to_odd_properties(n);
      lemma_iterate_to_odd_eq(n);
      assert current_n == iterate_to_odd_termination(n);
      assert current_n == iterate_to_odd(n);
    } else {
      var m := 3 * n + 1;
      var current_m := m;
      while current_m % 2 == 0
        invariant current_m > 0
        invariant iterate_to_odd(current_m) == iterate_to_odd(m)
        invariant iterate_to_odd_termination(current_m) == iterate_to_odd_termination(m)
        decreases current_m
      {
        if (current_m / 2) % 2 == 1 {
          lemma_iterate_to_odd_eq(current_m);
          current_m := current_m / 2;
        } else {
          lemma_iterate_to_odd_eq(current_m);
          current_m := current_m / 2;
        }
      }
      next := current_m;
      lemma_iterate_to_odd_properties(3 * n + 1);
      lemma_iterate_to_odd_eq(3 * n + 1);
      assert current_m == iterate_to_odd_termination(3 * n + 1);
      assert current_m == iterate_to_odd(3 * n + 1);
    }
    lemma_next_odd_collatz_properties(n);
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