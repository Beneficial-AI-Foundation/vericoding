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
  requires n % 2 == 0
  requires n > 0
  decreases n
  ensures iterate_to_odd_termination(n) % 2 == 1
{
  if (n / 2) % 2 == 1 then n / 2 else iterate_to_odd_termination(n / 2)
}
lemma lemma_iterate_to_odd_eq(n: nat)
  requires n % 2 == 0
  requires n > 0
  ensures iterate_to_odd(n) == iterate_to_odd_termination(n)
{
  if (n / 2) % 2 == 1 then
    // do nothing
  else
    lemma_iterate_to_odd_eq(n / 2);
}

lemma lemma_iterate_to_odd_properties(n: nat)
  requires n % 2 == 0
  requires n > 0
  ensures iterate_to_odd(n) % 2 == 1
  ensures iterate_to_odd(n) > 0
  decreases n
{
  if n / 2 % 2 == 1 then
    assert (n/2) % 2 == 1;
    assert n / 2 > 0;
  else
    lemma_iterate_to_odd_properties(n / 2);
}

lemma lemma_next_odd_collatz_properties(n: nat)
  requires n > 0
  ensures next_odd_collatz(n) % 2 == 1
  ensures next_odd_collatz(n) > 0
{
  if n % 2 == 0 then
    lemma_iterate_to_odd_properties(n);
  else
    lemma_iterate_to_odd_properties(3 * n + 1);
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
        invariant current_n % 2 == 0 ==> iterate_to_odd(current_n) == iterate_to_odd(n)
        decreases current_n
      {
        if (current_n / 2) % 2 == 1 {
          current_n := current_n / 2;
          lemma_iterate_to_odd_eq(n); // To relate it to the function definition if needed
          break;
        } else {
          var old_current_n := current_n;
          current_n := current_n / 2;
          assert old_current_n / 2 == current_n;
          lemma_iterate_to_odd_eq(n); // Ensure the invariant holds after the step
          lemma_iterate_to_odd_eq(old_current_n);
          lemma_iterate_to_odd_eq(current_n);
          // Proof for invariant: current_n % 2 == 0 ==> iterate_to_odd(current_n) == iterate_to_odd(n)
          // If old_current_n % 2 == 0 and (old_current_n / 2) % 2 != 1,
          // then iterate_to_odd(old_current_n) == iterate_to_odd(old_current_n / 2)
          // So, if iterate_to_odd(old_current_n) == iterate_to_odd(n), then we need
          // iterate_to_odd(current_n) == iterate_to_odd(n), which is iterate_to_odd(old_current_n / 2) == iterate_to_odd(n).
          // This holds by transitivity if iterate_to_odd(old_current_n) == iterate_to_odd(old_current_n / 2).
          // And iterate_to_odd(old_current_n) == iterate_to_odd(n) is the loop invariant for old_current_n.
        }
      }
      next := current_n;
      assert next % 2 == 1; // From the loop termination condition
      assert next == iterate_to_odd(n);
    } else {
      var m := 3 * n + 1;
      var current_m := m;
      while current_m % 2 == 0
        invariant current_m > 0
        invariant current_m % 2 == 0 ==> iterate_to_odd(current_m) == iterate_to_odd(m)
        decreases current_m
      {
        if (current_m / 2) % 2 == 1 {
          current_m := current_m / 2;
          lemma_iterate_to_odd_eq(m);
          break;
        } else {
          var old_current_m := current_m;
          current_m := current_m / 2;
          assert old_current_m / 2 == current_m;
          lemma_iterate_to_odd_eq(m);
          lemma_iterate_to_odd_eq(old_current_m);
          lemma_iterate_to_odd_eq(current_m);
        }
      }
      next := current_m;
      assert next % 2 == 1;
      assert next == iterate_to_odd(3 * n + 1);
    }
    lemma_next_odd_collatz_properties(n); // Ensure the postconditions hold based on the function definition
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