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
lemma next_odd_collatz_iter_correctness(n: nat)
  requires n > 0
  ensures var result := next_odd_collatz_iter(n); result % 2 == 1 && result == next_odd_collatz(n)
{
  var result := next_odd_collatz_iter(n);
}

lemma iterate_to_odd_positive(n: nat)
  requires n % 2 == 0
  requires n > 0
  ensures iterate_to_odd(n) > 0
{
  if (n / 2) % 2 == 1 {
    assert iterate_to_odd(n) == n / 2;
    assert n / 2 > 0;
  } else {
    assert iterate_to_odd(n) == iterate_to_odd(n / 2);
    iterate_to_odd_positive(n / 2);
  }
}

lemma next_odd_collatz_positive(n: nat)
  requires n > 0
  ensures next_odd_collatz(n) > 0
{
  if n % 2 == 0 {
    iterate_to_odd_positive(n);
  } else {
    assert 3 * n + 1 > 0;
    assert (3 * n + 1) % 2 == 0;
    iterate_to_odd_positive(3 * n + 1);
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
  odd_collatz := [];
  var current := n;
  
  if current % 2 == 0 {
    current := next_odd_collatz_iter(current);
  }
  
  while current != 1
    decreases *
    invariant current > 0
    invariant current % 2 == 1
    invariant forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] % 2 == 1
    invariant forall i :: 1 <= i < |odd_collatz| ==> odd_collatz[i] == next_odd_collatz(odd_collatz[i - 1])
    invariant |odd_collatz| == 0 ==> current == (if n % 2 == 1 then n else next_odd_collatz(n))
    invariant |odd_collatz| > 0 ==> current == next_odd_collatz(odd_collatz[|odd_collatz| - 1])
  {
    odd_collatz := odd_collatz + [current];
    next_odd_collatz_positive(current);
    current := next_odd_collatz_iter(current);
  }
  
  odd_collatz := odd_collatz + [current];
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