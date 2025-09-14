predicate sorted(a: array<int>)
   requires a != null
   reads a
{
   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}

// <vc-helpers>
lemma SortedLe(a: array<int>, j: int, k: int)
  requires sorted(a)
  requires 0 <= j <= k < a.Length
  ensures a[j] <= a[k]
{
  if j < k {
    assert 0 <= j < k < a.Length;
    assert a[j] <= a[k];
  } else {
    assert j == k;
    assert a[j] <= a[k];
  }
}
// </vc-helpers>

// <vc-spec>
method BinarySearch(a: array<int>, value: int) returns (index: int)
   requires a != null && 0 <= a.Length && sorted(a)
   ensures 0 <= index ==> index < a.Length && a[index] == value
   ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
// </vc-spec>
// <vc-code>
{
  var lo := 0;
  var hi := a.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant forall k :: 0 <= k < lo ==> a[k] < value
    invariant forall k :: hi <= k < a.Length ==> a[k] > value
    decreases hi - lo
  {
    var mid := lo + (hi - lo) / 2;
    assert hi - lo > 0;
    assert 0 <= (hi - lo) / 2;
    assert (hi - lo) / 2 < hi - lo;
    assert lo <= mid;
    assert mid < hi;
    assert 0 <= mid < a.Length;

    if a[mid] < value {
      forall k | 0 <= k < mid + 1
        ensures a[k] < value
      {
        assert 0 <= k <= mid;
        if k < lo {
          assert a[k] < value;
        } else {
          SortedLe(a, k, mid);
          assert a[k] <= a[mid];
          assert a[k] < value;
        }
      }
      lo := mid + 1;
    } else if a[mid] > value {
      forall k | mid <= k < a.Length
        ensures a[k] > value
      {
        SortedLe(a, mid, k);
        assert a[mid] <= a[k];
        assert a[k] > value;
      }
      hi := mid;
    } else {
      index := mid;
      return;
    }
  }
  index := -1;
  assert lo == hi;
  forall k | 0 <= k < a.Length
    ensures a[k] != value
  {
    if k < lo {
      assert a[k] < value;
      assert a[k] != value;
    } else {
      assert lo == hi;
      assert hi <= k < a.Length;
      assert a[k] > value;
      assert a[k] != value;
    }
  }
}
// </vc-code>

