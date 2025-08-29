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
predicate sorted(s: seq<int>) {
  forall i :: 0 <= i < |s| - 1 ==> s[i] <= s[i + 1]
}

method sort_sequence(s: seq<nat>) returns (sorted_s: seq<int>)
  ensures |sorted_s| == |s|
  ensures multiset(sorted_s) == multiset(s)
  ensures sorted(sorted_s)
{
  sorted_s := s;
  var i := 0;
  while i < |sorted_s|
    invariant 0 <= i <= |sorted_s|
    invariant |sorted_s| == |s|
    invariant multiset(sorted_s) == multiset(s)
    invariant forall j, k :: 0 <= j < k < i ==> sorted_s[j] <= sorted_s[k]
    invariant forall j, k :: 0 <= j < i <= k < |sorted_s| ==> sorted_s[j] <= sorted_s[k]
  {
    var min_idx := i;
    var j := i + 1;
    while j < |sorted_s|
      invariant i <= min_idx < |sorted_s|
      invariant i <= j <= |sorted_s|
      invariant forall k :: i <= k < j ==> sorted_s[min_idx] <= sorted_s[k]
    {
      if sorted_s[j] < sorted_s[min_idx] {
        min_idx := j;
      }
      j := j + 1;
    }
    if min_idx != i {
      var temp := sorted_s[i];
      sorted_s := sorted_s[i := sorted_s[min_idx]][min_idx := temp];
    }
    i := i + 1;
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
method get_odd_collatz(n: nat) returns (result: seq<int>)
  decreases *
  requires n > 1
  ensures sorted(result)
// </vc-spec>
// <vc-code>
{
  var unsorted := get_odd_collatz_unsorted(n);
  result := sort_sequence(unsorted);
}
// </vc-code>
