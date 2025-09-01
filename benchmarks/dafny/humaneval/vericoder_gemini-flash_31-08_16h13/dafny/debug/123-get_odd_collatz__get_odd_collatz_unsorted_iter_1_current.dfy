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
function iterate_to_odd_helper(n: nat): nat
  requires n % 2 == 0
  requires n > 0
  ensures iterate_to_odd_helper(n) % 2 == 1
{
  if (n / 2) % 2 == 1 then n / 2
  else iterate_to_odd_helper(n / 2)
}

function next_odd_collatz_helper(n: nat): nat
  requires n > 0
{
  if n % 2 == 0 then iterate_to_odd_helper(n)
  else iterate_to_odd_helper(3 * n + 1)
}

lemma next_odd_collatz_eq_next_odd_collatz_helper(n: nat)
  requires n > 0
  ensures next_odd_collatz_helper(n) == next_odd_collatz(n)
{
  if n % 2 == 0 {
    assert iterate_to_odd_helper(n) == iterate_to_odd(n); // This assertion is not strictly necessary for the lemma but helps with understanding.
  } else {
    assert iterate_to_odd_helper(3 * n + 1) == iterate_to_odd(3 * n + 1);
  }
}

lemma iterate_to_odd_properties(n: nat)
  requires n > 0
  requires n % 2 == 0
  ensures iterate_to_odd(n) % 2 == 1
  decreases n
{
  if (n / 2) % 2 == 1 {
    // n / 2 is odd, so iterate_to_odd(n) is n / 2, which is odd.
  } else {
    // n / 2 is even. Recurse.
    iterate_to_odd_properties(n / 2);
  }
}

lemma next_odd_collatz_properties(n: nat)
  requires n > 0
  ensures next_odd_collatz(n) % 2 == 1
  decreases *
{
  if n % 2 == 0 {
    iterate_to_odd_properties(n);
  } else {
    iterate_to_odd_properties(3 * n + 1);
  }
}

lemma next_odd_collatz_iter_correct(n: nat) returns (next: nat)
  requires n > 0
  ensures next % 2 == 1
  ensures next == next_odd_collatz(n)
{
  if n % 2 == 0 {
    next := iterate_to_odd(n);
    iterate_to_odd_properties(n);
  } else {
    next := iterate_to_odd(3 * n + 1);
    iterate_to_odd_properties(3 * n + 1);
  }
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
  var odd_collatz_list: seq<nat> := [];
  var current_n := n;

  while current_n != 1
    invariant current_n > 0
    invariant forall i :: 0 <= i < |odd_collatz_list| ==> odd_collatz_list[i] % 2 == 1
    invariant forall i :: 1 <= i < |odd_collatz_list| ==> odd_collatz_list[i] == next_odd_collatz(odd_collatz_list[i - 1])
    decreases current_n
  {
    var next_val: nat;
    next_odd_collatz_iter_correct(current_n);
    next_val := next_odd_collatz(current_n); // Use the specified function, its properties are established by the lemma

    odd_collatz_list := odd_collatz_list + [next_val];
    current_n := next_val;
  }
  odd_collatz := odd_collatz_list;
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