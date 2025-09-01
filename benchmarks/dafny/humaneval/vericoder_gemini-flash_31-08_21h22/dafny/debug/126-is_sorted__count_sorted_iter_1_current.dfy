method is_sorted(a: seq<int>) returns (f: bool)
  // post-conditions-start
  ensures f == forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j] && forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// </vc-helpers>

// <vc-spec>
method count_sorted(a: seq<int>, x: int, pos: int) returns (count: int)
  // pre-conditions-start
  requires forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
  requires 0 <= pos < |a|
  requires a[pos] == x
  requires pos == 0 || a[pos - 1] < x
  // pre-conditions-end
  // post-conditions-start
  ensures count == count_set(a, x)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var c := 0;
  var i := pos;
  while i < |a| && a[i] == x
    invariant 0 <= pos <= i <= |a|
    invariant c == i - pos
    invariant forall k :: pos <= k < i ==> a[k] == x
    invariant forall k :: 0 <= k < pos ==> a[k] < x // Based on precondition: pos == 0 || a[pos-1] < x and sortedness
  {
    c := c + 1;
    i := i + 1;
  }
  // At this point, `i` is the first index past `pos` such that a[i] != x, or i == |a|.
  // The count of `x` starting from `pos` is `i - pos`.
  // We need to prove that this count is equal to `count_set(a, x)`.

  // Proof for count_set(a, x)
  // Part 1: All elements counted are equal to x and within the sequence
  assert forall k :: pos <= k < i ==> a[k] == x;
  assert forall k :: 0 <= k < pos ==> a[k] != x; // From precondition a[pos-1]<x and sortedness

  // Part 2: Elements before 'pos' are not x
  if pos > 0 {
    assert a[pos-1] < x;
  }
  assert forall k :: 0 <= k < pos ==> a[k] < x;

  // Part 3: Elements after 'i' are not x (or i == |a|)
  if i < |a| {
    assert a[i] != x; // Loop termination condition
    assert a[i] > x by (forall j, k :: 0 <= j <= k < |a| ==> a[j] <= a[k]); // Because array is sorted and a[i] cannot be less than x since a[i-1] == x
  }
  assert forall k :: i <= k < |a| ==> a[k] > x;

  // Combining parts:
  // (0 <= k < pos ==> a[k] < x)
  // (pos <= k < i ==> a[k] == x)
  // (i <= k < |a| ==> a[k] > x)

  // Therefore, the set of indices `k` where `a[k] == x` is precisely `pos <= k < i`.
  // The size of this set is `i - pos`, which is `c`.
  assert count_set(a, x) == i - pos; // This assertion requires reasoning from the loop invariants and conditions
  count := c;
  return count;
}
// </vc-code>

function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// pure-end