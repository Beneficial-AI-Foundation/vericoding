function sorted(a: array<int>) : bool
    reads a
{
   forall i,j : int :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

// <vc-helpers>
lemma Sorted_implies_prefix_le(a: array<int>, mid: int)
  requires sorted(a)
  requires 0 <= mid < a.Length
  ensures forall i :: 0 <= i < mid ==> a[i] <= a[mid]
{
  assert forall i :: 0 <= i < mid ==> a[i] <= a[mid] by {
    forall i | 0 <= i < mid
      ensures a[i] <= a[mid]
    {
      assert 0 <= i < mid < a.Length;
    }
  }
}

lemma Sorted_implies_suffix_ge(a: array<int>, mid: int)
  requires sorted(a)
  requires 0 <= mid < a.Length
  ensures forall j :: mid <= j < a.Length ==> a[mid] <= a[j]
{
  assert forall j :: mid <= j < a.Length ==> a[mid] <= a[j] by {
    forall j | mid <= j < a.Length
      ensures a[mid] <= a[j]
    {
      if mid < j {
        assert 0 <= mid < j < a.Length;
      } else {
        assert mid == j;
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
method BinarySearch(a: array<int>, x: int) returns (index: int)
    requires sorted(a)
    ensures 0 <= index < a.Length ==> a[index] == x
    ensures index == -1 ==> forall i : int :: 0 <= i < a.Length ==> a[i] != x
// </vc-spec>
// <vc-code>
{
  var l := 0;
  var h := a.Length;
  while l < h
    invariant 0 <= l <= h <= a.Length
    invariant sorted(a)
    invariant forall i :: 0 <= i < l ==> a[i] < x
    invariant forall i :: h <= i < a.Length ==> a[i] > x
    decreases h - l
  {
    var mid := l + (h - l) / 2;
    assert l <= mid < h;
    assert 0 <= mid < a.Length;
    if a[mid] < x {
      Sorted_implies_prefix_le(a, mid);
      assert forall i :: 0 <= i <= mid ==> a[i] < x by {
        forall i | 0 <= i <= mid
          ensures a[i] < x
        {
          if i < mid {
            assert a[i] <= a[mid];
            assert a[i] < x;
          } else {
            assert i == mid;
            assert a[i] < x;
          }
        }
      }
      l := mid + 1;
    } else if x < a[mid] {
      Sorted_implies_suffix_ge(a, mid);
      assert forall i :: mid <= i < a.Length ==> a[i] > x by {
        forall i | mid <= i < a.Length
          ensures a[i] > x
        {
          if i == mid {
            assert a[i] > x;
          } else {
            assert a[mid] <= a[i];
            assert a[i] > x;
          }
        }
      }
      h := mid;
    } else {
      index := mid;
      return;
    }
  }
  assert l == h;
  index := -1;
  assert forall i :: 0 <= i < a.Length ==> a[i] != x by {
    forall i | 0 <= i < a.Length
      ensures a[i] != x
    {
      if i < l {
        assert a[i] < x;
      } else {
        assert l <= i < a.Length;
        assert h == l;
        assert h <= i < a.Length;
        assert a[i] > x;
      }
    }
  }
  return;
}
// </vc-code>

