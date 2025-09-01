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
  assert (set i | 0 <= i < end - start && a[start..end][i] == x) == (set i | start <= i < end && a[i] == x);
  assert (set i | start <= i < end && a[i] == x) <= (set i | 0 <= i < |a| && a[i] == x);
}

lemma count_set_split(a: seq<int>, x: int, mid: int)
  requires 0 <= mid <= |a|
  ensures count_set(a, x) == count_set(a[..mid], x) + count_set(a[mid..], x)
{
  var left_set := set i | 0 <= i < mid && a[i] == x;
  var right_set := set i | mid <= i < |a| && a[i] == x;
  var full_set := set i | 0 <= i < |a| && a[i] == x;
  
  assert left_set !! right_set;
  assert full_set == left_set + right_set;
  assert |full_set| == |left_set| + |right_set|;
  
  assert count_set(a[..mid], x) == |set i | 0 <= i < mid && a[..mid][i] == x|;
  assert count_set(a[..mid], x) == |left_set|;
  
  assert count_set(a[mid..], x) == |set i | 0 <= i < |a| - mid && a[mid..][i] == x|;
  assert count_set(a[mid..], x) == |right_set|;
}

lemma sorted_equal_elements_consecutive(a: seq<int>, x: int, i: int, j: int)
  requires forall k, l :: 0 <= k <= l < |a| ==> a[k] <= a[l]
  requires 0 <= i <= j < |a|
  requires a[i] == x && a[j] == x
  ensures forall k :: i <= k <= j ==> a[k] == x
{
  forall k | i <= k <= j
    ensures a[k] == x
  {
    assert a[i] <= a[k] <= a[j];
    assert x <= a[k] <= x;
  }
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
    forall k | pos <= k < end
      ensures a[k] == x
    {
      assert a[pos] <= a[k] <= a[end - 1];
      if k < end - 1 {
        assert a[k] <= a[end - 1] < a[end];
        assert a[k] <= x;
        assert a[pos] <= a[k];
        assert x <= a[k];
      } else if k == end - 1 {
        assert a[k] < a[end];
        assert a[k] < x + 1;
        assert a[pos] <= a[k];
        assert x <= a[k] < x + 1;
      }
    }
  } else {
    forall k | pos <= k < end
      ensures a[k] == x
    {
      assert a[pos] <= a[k];
      assert x <= a[k];
    }
  }
}

lemma count_set_range_equality(a: seq<int>, x: int, left: int, right: int)
  requires 0 <= left <= right < |a|
  requires forall k :: left <= k <= right ==> a[k] == x
  requires left == 0 || a[left - 1] < x
  requires right == |a| - 1 || a[right + 1] > x
  requires forall i, j :: 0 <= i <= j < |a| ==> a[i] <= a[j]
  ensures count_set(a, x) == right - left + 1
{
  var target_set := set i | left <= i <= right;
  var count_indices := set i | 0 <= i < |a| && a[i] == x;
  
  forall i | i in target_set
    ensures i in count_indices
  {
    assert left <= i <= right;
    assert a[i] == x;
    assert 0 <= i < |a|;
  }
  
  forall i | i in count_indices
    ensures i in target_set
  {
    assert 0 <= i < |a| && a[i] == x;
    if i < left {
      assert a[i] <= a[left - 1] < x;
      assert false;
    } else if i > right {
      assert a[right + 1] <= a[i];
      if right + 1 < |a| {
        assert x < a[right + 1] <= a[i];
        assert false;
      } else {
        assert i >= |a|;
        assert false;
      }
    }
  }
  
  assert target_set == count_indices;
  assert |target_set| == right - left + 1;
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
  
  if left < right {
    sorted_equal_elements_consecutive(a, x, left, right);
  }
  
  count_set_range_equality(a, x, left, right);
}
// </vc-code>

function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// pure-end