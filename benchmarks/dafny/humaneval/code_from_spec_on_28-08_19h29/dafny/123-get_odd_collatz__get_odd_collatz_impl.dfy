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
method get_odd_collatz_unsorted(n: nat) returns (odd_collatz: seq<nat>)
  decreases *
  requires n > 1
  ensures forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] % 2 == 1
  ensures forall i :: 1 <= i < |odd_collatz| ==> odd_collatz[i] == next_odd_collatz(odd_collatz[i - 1])
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma NextOddCollatzPreservesOddness(n: nat)
  requires n > 0
  ensures next_odd_collatz(n) % 2 == 1
{
  if n % 2 == 0 {
    var res := iterate_to_odd(n);
    assert res % 2 == 1;
  } else {
    var res := iterate_to_odd(3 * n + 1);
    assert res % 2 == 1;
  }
}

lemma NextOddCollatzDecreasesToOne(n: nat)
  requires n > 1
  ensures next_odd_collatz(n) < n || next_odd_collatz(n) == 1
{
  if n % 2 == 0 {
    var res := iterate_to_odd(n);
    assert res <= n / 2;
  } else {
    var res := iterate_to_odd(3 * n + 1);
    assert 3 * n + 1 > n;
    assert res <= (3 * n + 1) / 2;
    if n > 1 {
      assert res < n || res == 1;
    }
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method get_odd_collatz(n: nat) returns (sorted: seq<int>)
Retrieve elements. Requires: requires n > 1. Ensures: the result is sorted according to the ordering relation; the result is sorted according to the ordering relation.
*/
// </vc-description>

// <vc-spec>
method get_odd_collatz(n: nat) returns (sorted: seq<nat>)
  requires n > 1
  ensures forall i :: 0 <= i < |sorted| ==> sorted[i] % 2 == 1
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures exists unsorted: seq<nat> :: |unsorted| == |sorted| && 
    (forall i :: 0 <= i < |unsorted| ==> unsorted[i] % 2 == 1) &&
    (forall i :: 1 <= i < |unsorted| ==> unsorted[i] == next_odd_collatz(unsorted[i - 1])) &&
    multiset(sorted) == multiset(unsorted) && unsorted[0] == n
// </vc-spec>
// <vc-code>
{
  var unsorted: seq<nat> := [n];
  var current := n;
  while current != 1
    decreases current
    invariant current > 0
    invariant forall i :: 0 <= i < |unsorted| ==> unsorted[i] % 2 == 1
    invariant forall i :: 1 <= i < |unsorted| ==> unsorted[i] == next_odd_collatz(unsorted[i - 1])
    invariant unsorted[0] == n
  {
    current := next_odd_collatz(current);
    unsorted := unsorted + [current];
  }
  
  var sorted: seq<nat> := [];
  var remaining := unsorted;
  
  while |remaining| > 0
    decreases |remaining|
    invariant |sorted| + |remaining| == |unsorted|
    invariant forall i :: 0 <= i < |sorted| ==> sorted[i] % 2 == 1
    invariant forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
    invariant forall i :: 0 <= i < |remaining| ==> remaining[i] % 2 == 1
    invariant multiset(sorted + remaining) == multiset(unsorted)
  {
    var min_val := remaining[0];
    var min_idx := 0;
    
    for i := 1 to |remaining|
      invariant 0 <= min_idx < |remaining|
      invariant forall k :: 0 <= k < i ==> remaining[min_idx] <= remaining[k]
    {
      if remaining[i] < min_val {
        min_val := remaining[i];
        min_idx := i;
      }
    }
    
    sorted := sorted + [min_val];
    remaining := remaining[..min_idx] + remaining[min_idx+1..];
  }
  
  return sorted;
}
// </vc-code>
