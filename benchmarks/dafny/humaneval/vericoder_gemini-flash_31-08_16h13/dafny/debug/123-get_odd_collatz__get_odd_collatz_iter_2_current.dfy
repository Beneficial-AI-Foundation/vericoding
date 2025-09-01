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
function iterate_to_odd_helper(n: nat): nat
  requires n % 2 == 0
  requires n > 0
  ensures iterate_to_odd_helper(n) % 2 == 1
{
  if (n / 2) % 2 == 1 then n / 2 else iterate_to_odd_helper(n / 2)
}

function next_odd_collatz_helper(n: nat): nat
  requires n > 0
{
  if n % 2 == 0 then iterate_to_odd_helper(n) else iterate_to_odd_helper(3 * n + 1)
}

method next_odd_collatz_iter_helper(n: nat) returns (next: nat)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures next % 2 == 1
  ensures next == next_odd_collatz_helper(n)
  // post-conditions-end
{
  if n % 2 == 0 {
    var k := n;
    while k % 2 == 0 && (k / 2) % 2 == 0
      decreases k
      invariant k % 2 == 0 && k > 0
      invariant next_odd_collatz_helper(n) == iterate_to_odd_helper(k)
    {
      k := k / 2;
    }
    next := k / 2;
  } else {
    var m := 3 * n + 1;
    assert m % 2 == 0;
    var k := m;
    while k % 2 == 0 && (k / 2) % 2 == 0
      decreases k
      invariant k % 2 == 0 && k > 0
      invariant next_odd_collatz_helper(n) == iterate_to_odd_helper(k)
    {
      k := k / 2;
    }
    next := k / 2;
  }
}
method get_odd_collatz_unsorted_helper(n: nat) returns (odd_collatz: seq<nat>)
  decreases n
  requires n > 1
  ensures forall i :: 0 <= i < |odd_collatz| ==> odd_collatz[i] % 2 == 1
  ensures forall i :: 1 <= i < |odd_collatz| ==> odd_collatz[i] == next_odd_collatz_helper(odd_collatz[i - 1])
{
  var current_odd := 0;
  if n % 2 == 1 {
    current_odd := n;
  } else {
    var k := n;
    while k % 2 == 0 && (k / 2) % 2 == 0
      decreases k
      invariant k % 2 == 0 && k > 0
    {
      k := k / 2;
    }
    current_odd := k / 2;
  }

  if current_odd == 1 {
    return [1];
  } else {
    var next_val := next_odd_collatz_iter_helper(current_odd);
    var tail := get_odd_collatz_unsorted_helper(next_val);
    if current_odd == 1 { // This case is already handled by return [1] above, but included for completeness.
      return tail; // If current_odd is 1, tail will be [1].
    }
    return [current_odd] + tail;
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
  var unsorted_seq := get_odd_collatz_unsorted_helper(n);
  var int_arr: array<int> := new int[|unsorted_seq|];
  for i := 0 to |unsorted_seq| - 1 {
    int_arr[i] := unsorted_seq[i];
  }

  // Sort the sequence using a selection sort approach
  var a := int_arr;
  for i := 0 to |a| - 1
    invariant 0 <= i <= |a|
    invariant forall k, l :: 0 <= k < l < i ==> a[k] <= a[l]
    invariant forall k :: i <= k < |a| ==> a[k] % 2 == 1
    invariant forall k :: 0 <= k < i ==> a[k] % 2 == 1
    invariant multiset(a[..]) == multiset(int_arr[..]) // Compare multisets of array elements
  {
    var min_index := i;
    for j := i + 1 to |a| - 1
      invariant i <= min_index < |a|
      invariant forall k :: i <= k < j ==> a[min_index] <= a[k]
      invariant forall k :: i <= k < |a| ==> a[k] % 2 == 1
      invariant a[min_index] % 2 == 1
    {
      if a[j] < a[min_index] {
        min_index := j;
      }
    }
    var temp := a[i];
    a[i] := a[min_index];
    a[min_index] := temp;
  }
  sorted := a[..];
}
// </vc-code>

