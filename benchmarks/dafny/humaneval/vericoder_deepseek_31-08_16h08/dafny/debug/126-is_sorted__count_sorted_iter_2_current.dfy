method is_sorted(a: seq<int>) returns (f: bool)
  // post-conditions-start
  ensures f == forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j] && forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma count_set_sorted(a: seq<int>, x: int, pos: int)
  requires forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
  requires 0 <= pos < |a|
  requires a[pos] == x
  requires pos == 0 || a[pos - 1] < x
  ensures count_set(a, x) == count_set(a[pos..], x)
{
  var left := a[..pos];
  var right := a[pos..];
  
  // All elements in left are less than x
  assert forall i :: 0 <= i < |left| ==> left[i] < x;
  
  // All elements in right starting from position 0 equal x until they become greater
  var j := 0;
  while j < |right|
    invariant 0 <= j <= |right|
    invariant forall k :: 0 <= k < j ==> right[k] == x
    invariant j == |right| || right[j] >= x
    invariant j == |right| || (right[j] > x ==> forall k :: j <= k < |right| ==> right[k] > x)
  {
    if j < |right| - 1 {
      assert right[j] <= right[j+1];
    }
    if right[j] > x {
      break;
    }
    j := j + 1;
  }
  
  assert forall k :: j <= k < |right| ==> right[k] > x;
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
    invariant count == count_set(a[pos..i], x)
    invariant forall j :: pos <= j < i ==> a[j] == x
    decreases |a| - i
  {
    count := count + 1;
    i := i + 1;
  }
  
  i := pos - 1;
  while i >= 0 && a[i] == x
    invariant -1 <= i < pos
    invariant count == count_set(a[i+1..pos+1], x)
    invariant forall j :: i < j <= pos ==> a[j] == x
    decreases i + 1
  {
    count := count + 1;
    i := i - 1;
  }
}
// </vc-code>

function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// pure-end