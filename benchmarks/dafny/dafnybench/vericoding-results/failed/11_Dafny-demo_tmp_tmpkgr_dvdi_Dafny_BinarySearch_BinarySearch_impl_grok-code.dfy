predicate sorted(a: array?<int>, l: int, u: int)
    reads a
    requires a != null
    {
    forall i, j :: 0 <= l <= i <= j <= u < a.Length ==> a[i] <= a[j]
    }

// <vc-helpers>
// Empty, no changes needed
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
  if a.Length == 0 {
    index := -1;
    return;
  }
  var low := 0;
  var high := a.Length - 1;
  while low <= high
    invariant 0 <= low <= high + 1
    invariant low <= high < a.Length
    invariant sorted(a, 0, a.Length - 1)
    invariant forall k :: 0 <= k < a.Length && (k < low || k > high) ==> a[k] != key
  {
    var mid := (low + high) / 2;
    if a[mid] == key {
      index := mid;
      return;
    } else if a[mid] < key {
      low := mid + 1;
    } else {
      high := mid - 1;
    }
  }
  index := -1;
}
// </vc-code>

