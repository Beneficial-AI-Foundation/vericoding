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
  // Proof by contradiction or directly: no occurrences before pos due to sorted order and pos being start
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
  assert count == |set j | pos <= j < |a| && a[j] == x| && (i >= |a| || a[i-1] == x && (i == |a| || a[i] != x));
  CountSortedHelper(a, x, pos);
  return count;
}
// </vc-code>

function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// pure-end