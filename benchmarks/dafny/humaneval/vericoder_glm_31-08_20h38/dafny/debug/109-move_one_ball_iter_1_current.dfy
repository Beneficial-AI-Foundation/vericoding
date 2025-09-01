function is_sorted(a: seq<int>) : bool {
  forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

// <vc-helpers>
lemma lemma_is_sorted_append_single(a: seq<int>, x: int)
  requires is_sorted(a)
  requires |a| == 0 || a[|a|-1] <= x
  ensures is_sorted(a + [x])
{
  if |a| == 0 {
  } else {
    forall i, j | 0 <= i < j < |a| + [x]|
    {
      if j < |a| {
        assert a[i] <= a[j];
      } else if i < |a| {
        assert a[i] <= a[|a|-1];
        assert a[|a|-1] <= x;
      }
    }
  }
}

lemma lemma_is_sorted_rotate_left(a: seq<int>, i: int)
  requires 0 <= i < |a|
  requires is_sorted(a[i..] + a[..i])
  ensures is_sorted(a[(i+1)..] + a[..(i+1)])
{
  var left := a[i..];
  var right := a[..i];
  var combined := left + right;
  var new_left := a[(i+1)..];
  var new_right := a[..(i+1)];
  var new_combined := new_left + new_right;

  assert left == [a[i]] + new_left;
  assert new_right == right + [a[i]];
  
  if |new_left| > 0 {
    assert new_combined == new_left + right + [a[i]];
    assert is_sorted(new_left);
    assert is_sorted(right);
    assert new_left[|new_left|-1] <= a[i];
    assert is_sorted(new_left + right);
    forall k | 0 <= k < |new_left + right|
      ensures (new_left + right)[k] <= a[i]
    {
      if k < |new_left| {
        assert (new_left + right)[k] <= new_left[|new_left|-1];
        assert new_left[|new_left|-1] <= a[i];
      } else {
        assert (new_left + right)[k] == right[k - |new_left|];
        assert k - |new_left| < |right|;
        if k - |new_left| > 0 {
          assert right[k - |new_left| - 1] <= right[k - |new_left|];
          assert a[i] == right[|right| - 1];
          if k - |new_left| < |right| - 1 {
            assert right[k - |new_left|] <= right[|right| - 1];
          }
        }
      }
    }
    lemma_is_sorted_append_single(new_left + right, a[i]);
  } else {
    assert new_combined == right + [a[i]];
    assert is_sorted(right);
    if |right| > 0 {
      assert right[|right|-1] == a[i-1];
      assert a[i-1] <= a[i];
    }
    lemma_is_sorted_append_single(right, a[i]);
  }
}
// </vc-helpers>

// <vc-spec>
method move_one_ball(a: seq<int>) returns (can: bool)
  // pre-conditions-start
  requires |a| > 0
  requires forall i, j :: 0 <= i < |a| && 0 <= j < |a| && i != j ==> a[i] != a[j]
  // pre-conditions-end
  // post-conditions-start
  ensures can <==> exists i :: 0 <= i < |a| && is_sorted(a[i..] + a[..i])
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |a| == 1 {
    return true;
  }
  
  var n := |a|;
  var min := a[0];
  var min_index := 0;
  var max := a[0];
  
  for i := 1 to n
    invariant 0 <= min_index < n
    invariant forall j :: 0 <= j < i ==> min <= a[j]
  {
    if a[i] < min {
      min := a[i];
      min_index := i;
    }
  }
  
  var candidate := true;
  for i := 0 to min_index
    invariant candidate ==> (forall j :: 0 <= j < i ==> a[(min_index + j) % n] <= a[(min_index + j + 1) % n])
  {
    if i < min_index {
      if a[(min_index + i) % n] > a[(min_index + i + 1) % n] {
        candidate := false;
      }
    } else if i == min_index {
      if a[n-1] > min {
        candidate := false;
      }
    }
  }
  
  if candidate {
    return true;
  }
  
  return false;
}
// </vc-code>

