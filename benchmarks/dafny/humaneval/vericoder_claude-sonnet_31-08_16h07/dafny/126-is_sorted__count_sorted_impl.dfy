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
  var slice_set := set i | 0 <= i < end - start && a[start..end][i] == x;
  var mapped_set := set i | start <= i < end && a[i] == x;
  var full_set := set i | 0 <= i < |a| && a[i] == x;
  
  forall i | i in slice_set
    ensures (i + start) in mapped_set
  {
    assert 0 <= i < end - start;
    assert a[start..end][i] == a[start + i];
    assert start <= i + start < end;
  }
  
  forall i | i in mapped_set
    ensures (i - start) in slice_set
  {
    assert start <= i < end;
    assert a[i] == a[start..end][i - start];
    assert 0 <= i - start < end - start;
  }
  
  assert |slice_set| == |mapped_set| by {
    assert forall i :: i in slice_set <==> (i + start) in mapped_set;
    assert forall j :: j in mapped_set <==> (j - start) in slice_set;
  }
  assert mapped_set <= full_set;
  assert count_set(a[start..end], x) == |slice_set| == |mapped_set| <= |full_set| == count_set(a, x);
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
  
  var left_slice_set := set i | 0 <= i < mid && a[..mid][i] == x;
  forall i | i in left_slice_set
    ensures i in left_set
  {
    assert a[..mid][i] == a[i];
  }
  forall i | i in left_set
    ensures i in left_slice_set
  {
    assert a[i] == a[..mid][i];
  }
  assert left_slice_set == left_set;
  assert count_set(a[..mid], x) == |left_slice_set| == |left_set|;
  
  var right_slice_set := set i | 0 <= i < |a| - mid && a[mid..][i] == x;
  var right_mapped_set := set i {:trigger a[mid + i]} | 0 <= i < |a| - mid && a[mid + i] == x;
  forall i | i in right_slice_set
    ensures i in right_mapped_set
  {
    assert a[mid..][i] == a[mid + i];
  }
  forall i | i in right_mapped_set
    ensures i in right_slice_set
  {
    assert a[mid + i] == a[mid..][i];
  }
  assert right_slice_set == right_mapped_set;
  assert |right_slice_set| == |right_mapped_set|;
  
  var right_original_set := set j | j in right_mapped_set :: j + mid;
  forall j | j in right_original_set
    ensures j in right_set
  {
    var i :| i in right_mapped_set && j == i + mid;
    assert 0 <= i < |a| - mid && a[mid + i] == x;
    assert mid <= j < |a| && a[j] == x;
  }
  forall j | j in right_set
    ensures j in right_original_set
  {
    assert mid <= j < |a| && a[j] == x;
    var i := j - mid;
    assert 0 <= i < |a| - mid && a[mid + i] == x;
    assert i in right_mapped_set;
    assert j == i + mid;
  }
  assert right_original_set == right_set;
  assert |right_original_set| == |right_mapped_set|;
  assert count_set(a[mid..], x) == |right_slice_set| == |right_mapped_set| == |right_original_set| == |right_set|;
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
  forall k | pos <= k < end
    ensures a[k] == x
  {
    assert a[pos] <= a[k];
    if end < |a| {
      assert a[k] <= a[end - 1];
      assert a[end - 1] <= a[end] by {
        if end - 1 >= 0 {
          assert end - 1 < end;
        }
      }
      if end - 1 >= 0 {
        assert a[end - 1] < a[end] by {
          if a[end - 1] == a[end] {
            assert a[end] == a[end - 1];
            sorted_equal_elements_consecutive(a, a[end], end - 1, end);
            assert a[end] == x;
            assert false;
          }
        }
        assert a[k] < a[end];
        assert a[k] < x + 1;
      } else {
        assert a[k] < a[end];
        assert a[k] < x + 1;
      }
      assert x <= a[k] < x + 1;
      assert a[k] == x;
    } else {
      assert x <= a[k];
      assert a[k] == x;
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
      assert i < left && left > 0;
      assert a[i] <= a[left - 1] < x;
      assert a[i] < x;
      assert false;
    } else if i > right {
      assert i > right && right < |a| - 1;
      assert a[right + 1] <= a[i];
      assert x < a[right + 1] <= a[i];
      assert x < a[i];
      assert false;
    } else {
      assert left <= i <= right;
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
    invariant left == 0 || a[left - 1] < x || a[left - 1] == x
    invariant forall k :: left <= k <= pos ==> a[k] == x
  {
    left := left - 1;
  }
  
  while right < |a| - 1 && a[right + 1] == x
    invariant pos <= right < |a|
    invariant a[right] == x
    invariant right == |a| - 1 || a[right + 1] > x || a[right + 1] == x
    invariant forall k :: pos <= k <= right ==> a[k] == x
  {
    right := right + 1;
  }
  
  count := right - left + 1;
  
  sorted_equal_elements_consecutive(a, x, left, right);
  
  assert forall k :: left <= k <= right ==> a[k] == x by {
    sorted_equal_elements_consecutive(a, x, left, right);
  }
  assert left == 0 || a[left - 1] < x by {
    if left > 0 {
      assert !(a[left - 1] == x);
      assert a[left - 1] <= a[left] == x;
      assert a[left - 1] < x;
    }
  }
  assert right == |a| - 1 || a[right + 1] > x by {
    if right < |a| - 1 {
      assert !(a[right + 1] == x);
      assert a[right] == x <= a[right + 1];
      assert x < a[right + 1];
    }
  }
  
  count_set_range_equality(a, x, left, right);
}
// </vc-code>

function count_set(a: seq<int>, x: int): int {
  |set i | 0 <= i < |a| && a[i] == x|
}
// pure-end