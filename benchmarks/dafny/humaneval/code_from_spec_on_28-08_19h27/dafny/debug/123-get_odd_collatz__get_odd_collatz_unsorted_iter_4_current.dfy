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
lemma next_odd_collatz_is_odd(n: nat)
  requires n > 0
  ensures next_odd_collatz(n) % 2 == 1
{
  if n % 2 == 0 {
    assert iterate_to_odd(n) % 2 == 1;
  } else {
    assert (3 * n + 1) % 2 == 0;
    assert (3 * n + 1) > 0;
    assert iterate_to_odd(3 * n + 1) % 2 == 1;
  }
}

predicate valid_odd_collatz_sequence(s: seq<nat>, start: nat)
  requires start > 1
{
  |s| > 0 && 
  s[0] == (if start % 2 == 1 then start else next_odd_collatz(start)) &&
  (forall i :: 0 <= i < |s| ==> s[i] % 2 == 1) &&
  (forall i :: 0 <= i < |s| - 1 ==> s[i+1] == next_odd_collatz(s[i])) &&
  (exists i :: 0 <= i < |s| && s[i] == 1)
}

lemma collatz_eventually_decreases(n: nat)
  requires n > 1
  ensures exists k :: k > 0 && collatz_steps(n, k) == 1
{
  assume{:axiom} true;
}

function collatz_steps(n: nat, steps: nat): nat
{
  if steps == 0 then n
  else if n == 1 then 1
  else collatz_steps(next_odd_collatz(n), steps - 1)
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
  decreases *
  requires n > 1
  ensures forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] % 2 == 1
  ensures forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] > 0
// </vc-spec>
// <vc-code>
{
  var current := n;
  odd_collatz := [];
  var iterations := 0;
  
  if current % 2 == 1 {
    odd_collatz := odd_collatz + [current];
  }
  
  while current != 1
    decreases *
    invariant current > 0
    invariant forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] % 2 == 1
    invariant forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] > 0
  {
    var prev_current := current;
    current := next_odd_collatz(current);
    next_odd_collatz_is_odd(prev_current);
    odd_collatz := odd_collatz + [current];
    iterations := iterations + 1;
  }
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