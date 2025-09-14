predicate sorted(a: array?<int>, l: int, u: int)
    reads a
    requires a != null
    {
    forall i, j :: 0 <= l <= i <= j <= u < a.Length ==> a[i] <= a[j]
    }

// <vc-helpers>
predicate sorted_range(a: array?<int>, l: int, u: int)
    reads a
    requires a != null
    {
    (l > u) || (forall i, j :: l <= i <= j <= u && 0 <= l && u < a.Length ==> a[i] <= a[j])
    }
// </vc-helpers>

// <vc-spec>
method BinarySearch(a: array?<int>, key: int)
    returns (index: int)
    requires a != null && sorted(a,0,a.Length-1);
    ensures index >= 0 ==> index < a.Length && a[index] == key;
    ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key;
// </vc-spec>
// <vc-code>
{
  var low := 0;
  var high := a.Length - 1;

  while low <= high
    invariant 0 <= low <= a.Length
    invariant -1 <= high < a.Length
    invariant low <= high + 1
    invariant sorted_range(a,0,a.Length-1)
    invariant forall k :: 0 <= k < low ==> a[k] != key
    invariant forall k :: high < k < a.Length ==> a[k] != key
    invariant forall k :: 0 <= k < a.Length && a[k] == key ==> low <= k <= high
  {
    var mid := low + (high - low) / 2;
    if a[mid] == key {
      return mid;
    } else if a[mid] < key {
      low := mid + 1;
    } else {
      high := mid - 1;
    }
  }
  return -1;
}
// </vc-code>

