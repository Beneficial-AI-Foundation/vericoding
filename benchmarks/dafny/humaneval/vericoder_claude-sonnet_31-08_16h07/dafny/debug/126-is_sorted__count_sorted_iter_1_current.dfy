method is_sorted(a: seq<int>) returns (f: bool)
  // post-conditions-start
  ensures f == forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j] && forall i :: 0 <= i < |a| ==> count_set(a, a[i]) <= 2
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma count_set_properties(a: seq<int>, x: int, start: int, end: int)
  requires 0 <= start <= end <= |a|
  ensures count_set(a[start..end], x) <= count_set(a, x)
{
}

lemma count_set_split(a: seq<int>, x: int, mid: int)
  requires 0 <= mid <= |a|
  ensures count_set(a, x) == count_set(a[..mid], x) + count_set(a[mid..], x)
{
}

lemma sorted_equal_elements_consecutive(a: seq<int>, x: int, i: int, j: int)
  requires forall k, l :: 0 <= k <= l < |a| ==> a[k] <= a[l]
  requires 0 <= i < j < |a|
  requires a[i] == x && a[j] == x
  ensures forall k :: i <= k <= j ==> a[k] == x
{
}

lemma find_last_occurrence_helper(a: seq<int>, x: int, pos: int, end: int)
  requires forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
  requires 0 <= pos < end <= |a|
  requires a[pos] == x
  requires end == |a| || a[end] > x
  ensures forall k :: pos <= k < end ==> a[k] == x
  ensures forall k :: end <= k < |a| ==> a[k] > x
{
  if end < |a| {
    assert a[end] > x;
    if end > pos + 1 {
      assert a[pos] <= a[end - 1] <= a[end];
      assert a[pos] == x && a[end] > x;
      if a[end - 1] > x {
        find_last_occurrence_helper(a, x, pos, end - 1);
      } else {
        assert a[end - 1] <= x;
        assert a[end - 1] == x;
      }
    }
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
  var left := pos;
  var right := pos;
  
  while left > 0 && a[left - 1] == x
    invariant 0 <= left <= pos
    invariant a[left] == x
    invariant left == 0 || a[left - 1] < x
    invariant forall k :: left <= k <= pos ==> a[k] == x
  {
    left := left - 1;
  }
  
  while right < |a| - 1 && a[right + 1] == x
    invariant pos <= right < |a|
    invariant a[right] == x
    invariant right == |a| - 1 || a[right + 1] > x
    invariant forall k :: pos <= k <= right ==> a[k] == x
  {
    right := right + 1;
  }
  
  count := right - left + 1;
  
  assert forall k :: left <= k <= right ==> a[k] == x;
  assert left == 0 || a[left - 1] < x;
  assert right == |a| - 1 || a[right + 1] > x;
  
  sorted_equal_elements_consecutive(a, x, left, right);
  
  assert count_set(a, x) == |set i | 0 <= i < |a| && a[i] == x|;
  assert count_set(a, x) == |set i | left <= i <= right|;
  assert count_set(a, x) == right - left + 1;
}
// </vc-code>

function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// pure-end