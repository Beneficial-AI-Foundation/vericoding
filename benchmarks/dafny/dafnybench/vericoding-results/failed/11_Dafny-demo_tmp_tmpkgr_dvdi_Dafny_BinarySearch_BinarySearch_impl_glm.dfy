predicate sorted(a: array?<int>, l: int, u: int)
    reads a
    requires a != null
    {
    forall i, j :: 0 <= l <= i <= j <= u < a.Length ==> a[i] <= a[j]
    }

// <vc-helpers>
lemma LeftExcluded(a: array?<int>, key: int, low: int, high: int, mid: int)
    requires a != null && sorted(a,0,a.Length-1)
    requires 0 <= low <= mid <= high < a.Length
    requires a[mid] < key
    ensures forall k :: low <= k <= mid ==> a[k] != key
{
    forall k | low <= k <= mid
        ensures a[k] != key
    {
        assert a[k] <= a[mid];
        assert a[mid] < key;
    }
}

lemma RightExcluded(a: array?<int>, key: int, low: int, high: int, mid: int)
    requires a != null && sorted(a,0,a.Length-1)
    requires 0 <= low <= mid <= high < a.Length
    requires a[mid] > key
    ensures forall k :: mid <= k <= high ==> a[k] != key
{
    forall k | mid <= k <= high
        ensures a[k] != key
    {
        assert a[k] >= a[mid];
        assert a[mid] > key;
    }
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
  var low, high: int := 0, a.Length-1;
  while low <= high
      invariant 0 <= low <= high+1 <= a.Length
      invariant forall k :: 0 <= k < low ==> a[k] != key
      invariant forall k :: high+1 <= k < a.Length ==> a[k] != key
  {
      var mid := (low + high) / 2;
      if a[mid] == key {
          return mid;
      } else if a[mid] < key {
          LeftExcluded(a, key, low, high, mid);
          low := mid + 1;
      } else {
          RightExcluded(a, key, low, high, mid);
          high := mid - 1;
      }
  }
  return -1;
}
// </vc-code>

