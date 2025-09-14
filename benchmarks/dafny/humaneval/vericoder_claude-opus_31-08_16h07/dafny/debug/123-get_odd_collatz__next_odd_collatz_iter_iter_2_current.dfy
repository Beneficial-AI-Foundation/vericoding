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
  ensures n / 2 < n
{
  // This is trivially true for n > 0
}

lemma iterate_to_odd_step(n: nat)
  requires n % 2 == 0
  requires n > 0
  requires (n / 2) % 2 == 0
  ensures iterate_to_odd(n) == iterate_to_odd(n / 2)
{
  // This follows from the definition of iterate_to_odd
}

lemma iterate_to_odd_base(n: nat)
  requires n % 2 == 0
  requires n > 0
  requires (n / 2) % 2 == 1
  ensures iterate_to_odd(n) == n / 2
{
  // This follows from the definition of iterate_to_odd
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
  var m: nat;
  
  if n % 2 == 0 {
    m := n;
  } else {
    m := 3 * n + 1;
    assert m % 2 == 0;  // 3*n+1 is even when n is odd
  }
  
  // Now m is even, so we can call iterate_to_odd(m)
  assert m % 2 == 0;
  var initial_m := m;
  
  // Iterate until we find an odd number
  while m % 2 == 0
    invariant m > 0
    invariant m % 2 == 0 ==> iterate_to_odd(m) == iterate_to_odd(initial_m)
    invariant m % 2 == 1 ==> m == iterate_to_odd(initial_m)
    decreases m
  {
    var old_m := m;
    m := m / 2;
    
    if m % 2 == 0 {
      iterate_to_odd_step(old_m);
    } else {
      iterate_to_odd_base(old_m);
    }
  }
  
  next := m;
  assert next == iterate_to_odd(initial_m);
  assert initial_m == if n % 2 == 0 then n else 3 * n + 1;
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