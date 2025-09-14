predicate sorted(a: array<int>)
   requires a != null
   reads a
{
   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}

// <vc-helpers>

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
  var hi := a.Length - 1;
  index := -1;
  while lo <= hi
    invariant index == -1
    invariant 0 <= lo <= a.Length
    invariant -1 <= hi < a.Length
    invariant lo <= hi + 1
    invariant forall k :: 0 <= k < lo ==> a[k] < value
    invariant forall k :: hi < k < a.Length ==> a[k] > value
    decreases hi - lo + 1
  {
    var mid := lo + (hi - lo) / 2;
    assert lo <= mid && mid <= hi;
    if a[mid] == value {
      index := mid;
      return;
    } else if a[mid] < value {
      lo := mid + 1;
    } else {
      hi := mid - 1;
    }
  }
  return;
}
// </vc-code>

