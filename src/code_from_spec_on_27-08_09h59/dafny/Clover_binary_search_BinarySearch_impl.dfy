// <vc-helpers>
lemma SortedArrayProperty(a: array<int>, low: int, high: int, key: int)
  requires 0 <= low <= high <= a.Length
  requires forall i,j :: 0<=i<j<a.Length ==> a[i]<=a[j]
  requires low < a.Length && a[low] >= key
  ensures forall i :: low <= i < a.Length ==> a[i] >= key
{
  forall i | low <= i < a.Length
    ensures a[i] >= key
  {
    if i >= low && low < a.Length {
      assert a[low] >= key;
      if i > low {
        assert low < i < a.Length;
        assert a[low] <= a[i];
        assert a[i] >= a[low] >= key;
      }
    }
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method BinarySearch(a: array<int>, key: int) returns (n: int)
  requires forall i,j :: 0<=i<j<a.Length ==> a[i]<=a[j]
  ensures 0<= n <=a.Length
  ensures forall i :: 0<= i < n ==> a[i] < key
  ensures n == a.Length ==> forall i :: 0 <= i < a.Length ==> a[i] < key
  ensures forall i :: n<= i < a.Length ==> a[i]>=key
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  var low := 0;
  var high := a.Length;
  
  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant forall i :: 0 <= i < low ==> a[i] < key
    invariant forall i :: high <= i < a.Length ==> a[i] >= key
  {
    var mid := (low + high) / 2;
    
    if a[mid] < key {
      low := mid + 1;
    } else {
      high := mid;
      if high < a.Length {
        SortedArrayProperty(a, high, a.Length, key);
      }
    }
  }
  
  n := low;
}
// </vc-code>
