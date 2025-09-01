method is_sorted(a: seq<int>) returns (f: bool)
  // post-conditions-start
  ensures f == forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j] && forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma CountSortedHelper(a: seq<int>, x: int, pos: int)
  requires forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
  requires 0 <= pos < |a|
  requires a[pos] == x
  requires pos == 0 || a[pos - 1] < x
  ensures |set j | pos <= j < |a| && a[j] == x| == |set j | 0 <= j < |a| && a[j] == x|
{
  // Since a is sorted non-decreasing,
  // all elements before pos are <= a[pos-1] < a[pos] == x
  // so a[j] for j < pos can't be x.
  // Similarly, any x must be at pos or later.
  // The consecutive x's from pos to the end are all x's.
  forall j | pos <= j < |a| && a[j] == x {
    assert j >= pos && j < |a| && a[j] == x;
  }
  forall j | 0 <= j < |a| && a[j] == x {
    // Due to sorted and pos-1 < x, and a[pos] == x first occurrence
    assert j >= pos;
  }
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
  var count := 0;
  var i := pos;
  while i < |a| && a[i] == x
    decreases |a| - i
    invariant 0 <= pos <= i <= |a|
    invariant count == i - pos
    invariant forall j :: pos <= j < i ==> a[j] == x
  {
    count := count + 1;
    i := i + 1;
  }
  CountSortedHelper(a, x, pos);
  assert |set j | 0 <= j < |a| && a[j] == x| == |set j | pos <= j < |a| && a[j] == x|; // from lemma
  assert count == |set j | pos <= j < |a| && a[j] == x|; // from loop
  assert count == count_set(a, x);
  return count;
}
// </vc-code>

function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// pure-end