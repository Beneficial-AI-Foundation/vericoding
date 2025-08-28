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
lemma iterate_to_odd_preserves_odd(n: nat)
  requires n % 2 == 0
  requires n > 0
  ensures iterate_to_odd(n) % 2 == 1
{
}

lemma next_odd_collatz_is_odd(n: nat)
  requires n > 0
  ensures next_odd_collatz(n) % 2 == 1
{
  if n % 2 == 0 {
    iterate_to_odd_preserves_odd(n);
  } else {
    assert 3 * n + 1 > 0;
    assert (3 * n + 1) % 2 == 0;
    iterate_to_odd_preserves_odd(3 * n + 1);
  }
}

method sort_sequence(s: seq<nat>) returns (sorted: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] % 2 == 1
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i :: 0 <= i < |sorted| ==> sorted[i] % 2 == 1
  ensures multiset(s) == multiset(sorted)
{
  sorted := s;
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant forall k :: 0 <= k < |sorted| ==> sorted[k] % 2 == 1
    invariant multiset(s) == multiset(sorted)
    invariant forall p, q :: 0 <= p < q < i ==> sorted[p] <= sorted[q]
  {
    var j := i;
    while j > 0 && sorted[j-1] > sorted[j]
      invariant 0 <= j <= i
      invariant forall k :: 0 <= k < |sorted| ==> sorted[k] % 2 == 1
      invariant multiset(s) == multiset(sorted)
      invariant forall p, q :: 0 <= p < q < j ==> sorted[p] <= sorted[q]
      invariant forall p, q :: j < p < q <= i ==> sorted[p] <= sorted[q]
      invariant forall p :: 0 <= p < j && j <= i ==> sorted[p] <= sorted[j]
      invariant forall p :: j <= i && i < p < |sorted| ==> sorted[j] <= sorted[p]
    {
      sorted := sorted[j-1 := sorted[j]][j := sorted[j-1]];
      j := j - 1;
    }
    i := i + 1;
  }
}
// </vc-helpers>

// <vc-spec>
method get_odd_collatz(n: nat) returns (sorted: seq<int>)
  decreases *
  requires n > 1
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i :: 0 <= i < |sorted| ==> sorted[i] % 2 == 1
// </vc-spec>
// <vc-code>
{
  var unsorted := get_odd_collatz_unsorted(n);
  sorted := sort_sequence(unsorted);
}
// </vc-code>
