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
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures multiset(s) == multiset(sorted)
{
  sorted := [];
  for i := 0 to |s|
  {
    var inserted := false;
    for j := 0 to |sorted|
    {
      if (j == |sorted| || sorted[j] > s[i])
      {
        sorted := sorted[..j] + [s[i]] + sorted[j..];
        inserted := true;
        break;
      }
    }
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
  var seen: set<nat> := {};
  var current: nat := n;
  var list: seq<nat> := [];
  while current !in seen
    decreases *
  {
    seen := seen + {current};
    list := list + [current];
    current := next_odd_collatz(current);
  }
  var sortedSeq := SortSeq(list);
  sorted := sortedSeq;
}
// </vc-code>

