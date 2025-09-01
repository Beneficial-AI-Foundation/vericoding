

// <vc-helpers>
lemma count_set_properties(a: seq<int>, x: int)
  ensures count_set(a, x) >= 0
  ensures count_set(a, x) <= |a|
{
  var s := set i | 0 <= i < |a| && a[i] == x;
  assert s <= set i | 0 <= i < |a|;
  var indices := set i | 0 <= i < |a|;
  assert |s| <= |indices|;
  assert |indices| <= |a|;
}

lemma count_set_empty(x: int)
  ensures count_set([], x) == 0
{
  var s := set i | 0 <= i < |[]| && ([] : seq<int>)[i] == x;
  assert s == {};
}

lemma count_set_single(x: int, y: int)
  ensures count_set([y], x) == (if x == y then 1 else 0)
{
  if x == y {
    var s := set i | 0 <= i < |[y]| && [y][i] == x;
    assert s == {0};
  } else {
    var s := set i | 0 <= i < |[y]| && [y][i] == x;
    assert s == {};
  }
}

lemma count_set_bounds(a: seq<int>, x: int)
  ensures 0 <= count_set(a, x) <= |a|
{
  count_set_properties(a, x);
}
// </vc-helpers>

// <vc-spec>
method is_sorted(a: seq<int>) returns (f: bool)
  // post-conditions-start
  ensures f == forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j] && forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |a| == 0 {
    return true;
  }
  
  var i := 0;
  while i < |a| - 1
    invariant 0 <= i <= |a| - 1
    invariant forall k, l :: 0 <= k <= l < i + 1 ==> a[k] <= a[l]
  {
    if a[i] > a[i + 1] {
      return false;
    }
    i := i + 1;
  }
  
  var j := 0;
  while j < |a|
    invariant 0 <= j <= |a|
    invariant forall k :: 0 <= k < j ==> count_set(a, a[k]) <= 2
  {
    count_set_bounds(a, a[j]);
    if count_set(a, a[j]) > 2 {
      return false;
    }
    j := j + 1;
  }
  
  return true;
}
// </vc-code>

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
  assume{:axiom} false;
}
function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// pure-end