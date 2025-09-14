// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method BinarySearch(a: array<int>, key: int) returns (n: int)
  requires forall i,j :: 0<=i<j<a.Length ==> a[i]<=a[j]
  ensures 0<= n <=a.Length
  ensures forall i :: 0<= i < n ==> a[i] < key
  ensures n == a.Length ==> forall i :: 0 <= i < a.Length ==> a[i] < key
  ensures forall i :: n<= i < a.Length ==> a[i]>=key
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
    var mid := low + (high - low) / 2;
    if a[mid] < key {
      low := mid + 1;
    } else {
      high := mid;
    }
  }
  n := low;
}
// </vc-code>
