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
function iter_to_odd(n: nat): nat
  requires n > 0
  ensures iter_to_odd(n) % 2 == 1
  ensures (n % 2 == 0) ==> (iter_to_odd(n) == iter_to_odd(n / 2))
  ensures (n % 2 == 0 && (n / 2) % 2 == 1) ==> (iter_to_odd(n) == n / 2)
{
  if n % 2 == 1 then n
  else iter_to_odd(n / 2)
}

function next_odd_collatz_helper(n: nat): nat
  requires n > 0
  ensures next_odd_collatz_helper(n) % 2 == 1
  ensures next_odd_collatz_helper(n) == (if n % 2 == 0 then iter_to_odd(n) else iter_to_odd(3 * n + 1))
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
    var initial_val_for_iter_to_odd := 3 * current_n + 1;
    current_n := 3 * current_n + 1;
    while current_n % 2 == 0
      invariant current_n > 0
      invariant iter_to_odd(initial_val_for_iter_to_odd) == iter_to_odd(current_n)
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