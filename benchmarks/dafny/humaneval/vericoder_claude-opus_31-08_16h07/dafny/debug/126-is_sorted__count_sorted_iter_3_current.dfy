method is_sorted(a: seq<int>) returns (f: bool)
  // post-conditions-start
  ensures f == forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j] && forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma count_set_single(a: seq<int>, x: int, i: int)
  requires 0 <= i < |a|
  requires a[i] == x
  requires forall j :: 0 <= j < |a| && j != i ==> a[j] != x
  ensures count_set(a, x) == 1
{
  var s := set j {:trigger a[j]} | 0 <= j < |a| && a[j] == x;
  assert s == {i};
}

lemma SetCardinalityRange(start: int, end: int)
  requires 0 <= start <= end
  ensures |set i {:trigger i in (set i | start <= i < end)} | start <= i < end| == end - start
{
  var s := set i {:trigger i in s} | start <= i < end;
  if start == end {
    assert s == {};
  } else {
    var s' := set i {:trigger i in s'} | start <= i < end - 1;
    SetCardinalityRange(start, end - 1);
    assert s == s' + {end - 1};
    assert end - 1 !in s';
    assert |s| == |s'| + 1;
    assert |s'| == (end - 1) - start;
  }
}

lemma count_set_range(a: seq<int>, x: int, start: int, end: int)
  requires 0 <= start <= end <= |a|
  requires forall i :: start <= i < end ==> a[i] == x
  requires forall i :: 0 <= i < start ==> a[i] != x
  requires forall i :: end <= i < |a| ==> a[i] != x
  ensures count_set(a, x) == end - start
{
  var s := set i {:trigger a[i]} | 0 <= i < |a| && a[i] == x;
  var range := set i {:trigger i in range} | start <= i < end;
  assert s == range;
  SetCardinalityRange(start, end);
  assert |range| == end - start;
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
  count := 1;
  var i := pos + 1;
  
  while i < |a| && a[i] == x
    invariant pos < i <= |a|
    invariant count == i - pos
    invariant forall j :: pos <= j < i ==> a[j] == x
    invariant forall j :: 0 <= j < pos ==> a[j] < x
  {
    count := count + 1;
    i := i + 1;
  }
  
  // Now we know a[pos..i] contains all x's and nothing outside contains x
  assert forall j :: pos <= j < i ==> a[j] == x;
  assert i == |a| || a[i] != x;
  
  // Since array is sorted and a[i] != x (if i < |a|), all elements after i are > x
  if i < |a| {
    assert a[i] > x;
    assert forall j :: i <= j < |a| ==> a[j] >= a[i] > x;
  }
  
  count_set_range(a, x, pos, i);
}
// </vc-code>

function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// pure-end