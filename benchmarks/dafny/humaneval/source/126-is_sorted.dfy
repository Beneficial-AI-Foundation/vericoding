method is_sorted(a: seq<int>) returns (f: bool)
  // post-conditions-start
  ensures f == forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j] && forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2
  // post-conditions-end
{
  // impl-start
  if |a| == 0 {
    return true;
  }
  var is_asc := true;
  var i := 1;
  while i < |a|
    // invariants-start
    invariant 1 <= i <= |a|
    invariant is_asc == forall j, k :: 0 <= j < k < i ==> a[j] <= a[k]
    // invariants-end
  {
    if a[i - 1] > a[i] {
      is_asc := false;
    }
    i := i + 1;
  }

  if !is_asc {
    return false;
  }

  i := 0;

  var has_no_more_that_2 := true;
  while i < |a|
    // invariants-start
    invariant 0 <= i <= |a|
    invariant has_no_more_that_2 == forall j :: 0 <= j < i ==> count_set(a, a[j]) <= 2
    // invariants-end
  {
    var count := count_set(a, a[i]);
    if count > 2 {
      has_no_more_that_2 := false;
    }
    i := i + 1;
  }
  return has_no_more_that_2;
  // impl-end
}


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
{
  // impl-start
  count := 0;
  var i := pos;
  ghost var positions := {};

  while i < |a| && a[i] == x
    // invariants-start
    invariant 0 <= i <= |a|
    invariant positions == set j | 0 <= j < i && a[j] == x
    invariant count == |positions|
    // invariants-end
  {
    count := count + 1;
    positions := positions + {i};
    i := i + 1;
  }
  assert positions == set j | 0 <= j < |a| && a[j] == x; // assert-line
  // impl-end
}

function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// pure-end
