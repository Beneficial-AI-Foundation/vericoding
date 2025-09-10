function iterate_to_odd(n: nat): nat
  requires n % 2 == 0
  requires n > 0
  ensures iterate_to_odd(n) % 2 == 1
{
  if (n / 2) % 2 == 1 then n / 2 else iterate_to_odd(n / 2)
}
// pure-end
function next_odd_collatz(n: nat): nat
  requires n > 0
{
  if n % 2 == 0 then iterate_to_odd(n) else iterate_to_odd(3 * n + 1)
}
// pure-end
method next_odd_collatz_iter(n: nat) returns (next: nat)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures next % 2 == 1
  ensures next == next_odd_collatz(n)
  // post-conditions-end
{
  // impl-start
  next := n;
  if next % 2 == 1 {
    next := 3 * next + 1;
  }
  ghost var start := next;
  while next % 2 == 0
    decreases next
    // invariants-start
    invariant next > 0
    invariant next % 2 == 0 ==> next_odd_collatz(next) == next_odd_collatz(n)
    invariant next % 2 == 0 ==> iterate_to_odd(next) == iterate_to_odd(start)
    invariant next % 2 == 1 ==> next == iterate_to_odd(start)
    // invariants-end
  {
    next := next / 2;
  }
  // impl-end
}

method get_odd_collatz_unsorted(n: nat) returns (odd_collatz: seq<nat>)
  decreases *
  requires n > 1
  ensures forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] % 2 == 1
  ensures forall i :: 1 <= i < |odd_collatz| ==> odd_collatz[i] == next_odd_collatz(odd_collatz[i - 1])
{
  var cur := n;
  if cur % 2 == 0 {
    cur := next_odd_collatz_iter(cur);
  }
  odd_collatz := [cur];
  while odd_collatz[|odd_collatz| - 1] != 1
    decreases *
    invariant cur > 0
    invariant |odd_collatz| > 0
    invariant forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] % 2 == 1
    invariant forall i :: 1 <= i < |odd_collatz| ==> odd_collatz[i] == next_odd_collatz(odd_collatz[i - 1])
  {
    odd_collatz := odd_collatz + [next_odd_collatz(odd_collatz[|odd_collatz| - 1])];
  }
}

method get_odd_collatz(n: nat) returns (sorted: seq<int>)
  decreases *
  requires n > 1
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures forall i :: 0 <= i < |sorted| ==> sorted[i] % 2 == 1
{
  sorted := get_odd_collatz_unsorted(n);
  ghost var unsorted := sorted;
  var i := 0;
  while i < |sorted|
    invariant 0 <= i <= |sorted|
    invariant forall j, k :: 0 <= j < k < i ==> sorted[j] <= sorted[k]
    invariant multiset(unsorted) == multiset(sorted)
    invariant forall j :: 0 <= j < i ==> forall k :: i <= k < |sorted| ==> sorted[j] <= sorted[k]
    invariant |sorted| == |unsorted|
  {
    var minIndex := i;
    var j := i + 1;
    while j < |sorted|
      invariant i <= minIndex < j <= |sorted|
      invariant forall k :: i <= k < j ==> sorted[minIndex] <= sorted[k]
    {
      if sorted[j] < sorted[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    if minIndex != i {
      var temp := sorted[i];
      sorted := sorted[i := sorted[minIndex]][minIndex := temp];
    }
    i := i + 1;
  }
  assert forall i :: 0 <= i < |sorted| ==> sorted[i] in multiset(unsorted);
}
