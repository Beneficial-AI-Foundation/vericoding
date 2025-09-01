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
    assert n % 2 == 1;
    assert (3 * n + 1) % 2 == 0;
    assert 3 * n + 1 > 0;
    assert iterate_to_odd(3 * n + 1) % 2 == 1;
  }
}

lemma three_n_plus_one_even(n: nat)
  requires n % 2 == 1
  ensures (3 * n + 1) % 2 == 0
{
}

lemma three_n_plus_one_positive(n: nat)
  requires n > 0
  ensures 3 * n + 1 > 0
{
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
  odd_collatz := [];
  var current := n;
  
  while current != 1
    decreases *
    invariant current > 0
    invariant forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] % 2 == 1
    invariant forall i :: 1 <= i < |odd_collatz| ==> odd_collatz[i] == next_odd_collatz(odd_collatz[i - 1])
    invariant |odd_collatz| == 0 || odd_collatz[|odd_collatz| - 1] == current || next_odd_collatz(odd_collatz[|odd_collatz| - 1]) == current
  {
    if current % 2 == 1 {
      odd_collatz := odd_collatz + [current];
    }
    
    var next_val := next_odd_collatz_iter(current);
    next_odd_collatz_is_odd(current);
    current := next_val;
  }
  
  if |odd_collatz| == 0 || odd_collatz[|odd_collatz| - 1] != 1 {
    odd_collatz := odd_collatz + [1];
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