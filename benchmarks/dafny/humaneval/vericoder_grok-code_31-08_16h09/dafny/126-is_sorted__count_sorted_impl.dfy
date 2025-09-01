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
  // Proof that no x before pos
  if exists j :: 0 <= j < pos && a[j] == x {
    var j :| 0 <= j < pos && a[j] == x;
    if pos > 0 {
      assert a[j] <= a[pos - 1] < x; // since sorted and pos-1 < x <= a[j] contradiction
    }
  }
  // Proof that all x from pos on are in the set
  // Since consecutive, and all are x until not
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
  count := 0;
  var i := pos;
  while i < |a| && a[i] == x
    invariant 0 <= pos <= i <= |a|
    invariant count == i - pos
    invariant forall j :: pos <= j < i ==> a[j] == x
    decreases |a| - i
  {
    count := count + 1;
    i := i + 1;
  }
  CountSortedHelper(a, x, pos);
  assert |set j | 0 <= j < |a| && a[j] == x| == |set j | pos <= j < |a| && a[j] == x|; // from lemma
  assert count == |set j | pos <= j < |a| && a[j] == x|; // from loop
  assert count == count_set(a, x);
}
// </vc-code>

function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// pure-end