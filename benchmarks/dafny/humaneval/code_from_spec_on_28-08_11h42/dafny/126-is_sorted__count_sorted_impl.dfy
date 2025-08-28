method is_sorted(a: seq<int>) returns (f: bool)
  // post-conditions-start
  ensures f == forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j] && forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma count_set_properties(a: seq<int>, x: int, pos: int)
  requires forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
  requires 0 <= pos < |a|
  requires a[pos] == x
  requires pos == 0 || a[pos - 1] < x
  ensures count_set(a, x) > 0
  ensures forall i :: 0 <= i < |a| && a[i] == x ==> i >= pos
{
  var indices := set i | 0 <= i < |a| && a[i] == x;
  assert pos in indices;
  assert |indices| >= 1;
}

lemma count_set_consecutive(a: seq<int>, x: int, start: int, end: int)
  requires forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
  requires 0 <= start <= end < |a|
  requires forall i :: start <= i <= end ==> a[i] == x
  requires start == 0 || a[start - 1] < x
  requires end == |a| - 1 || a[end + 1] > x
  ensures count_set(a, x) == end - start + 1
{
  var indices := set i | 0 <= i < |a| && a[i] == x;
  var range_indices := set i {:trigger} | start <= i <= end :: i;
  
  forall i | 0 <= i < |a| && a[i] == x
    ensures start <= i <= end
  {
    if i < start {
      assert a[i] == x;
      assert a[start - 1] < x;
      assert i <= start - 1;
      assert a[i] <= a[start - 1] < x;
      assert false;
    }
    if i > end {
      assert a[i] == x;
      assert a[end + 1] > x;
      assert i >= end + 1;
      assert a[end + 1] <= a[i] == x;
      assert false;
    }
  }
  
  assert indices == range_indices;
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
  var end := pos;
  while end + 1 < |a| && a[end + 1] == x
    invariant pos <= end < |a|
    invariant a[end] == x
    invariant forall i :: pos <= i <= end ==> a[i] == x
    invariant end + 1 >= |a| || a[end + 1] != x || a[end + 1] == x
  {
    end := end + 1;
  }
  
  count := end - pos + 1;
  
  assert forall i :: pos <= i <= end ==> a[i] == x;
  assert pos == 0 || a[pos - 1] < x;
  if end + 1 < |a| {
    assert a[end + 1] != x;
    assert a[end] == x;
    assert a[end] <= a[end + 1];
    assert x < a[end + 1];
    assert end == |a| - 1 || a[end + 1] > x;
  } else {
    assert end == |a| - 1;
    assert end == |a| - 1 || a[end + 1] > x;
  }
  count_set_consecutive(a, x, pos, end);
}
// </vc-code>

function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// pure-end