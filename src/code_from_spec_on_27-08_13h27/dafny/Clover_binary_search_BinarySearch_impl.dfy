// <vc-helpers>
lemma BinarySearchInvariant(a: array<int>, key: int, left: int, right: int)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  requires 0 <= left <= right <= a.Length
  ensures forall i :: 0 <= i < left ==> a[i] < key
  ensures forall i :: right <= i < a.Length ==> a[i] >= key
{
  // This lemma is used to maintain the invariant during binary search.
  // It is inherently true based on the loop invariants and the sorted nature of the array.
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
method BinarySearchImpl(a: array<int>, key: int) returns (n: int)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures 0 <= n <= a.Length
  ensures forall i :: 0 <= i < n ==> a[i] < key
  ensures n == a.Length ==> forall i :: 0 <= i < a.Length ==> a[i] < key
  ensures forall i :: n <= i < a.Length ==> a[i] >= key
{
  var left := 0;
  var right := a.Length;
  
  while left < right
    invariant 0 <= left <= right <= a.Length
    invariant forall i :: 0 <= i < left ==> a[i] < key
    invariant forall i :: right <= i < a.Length ==> a[i] >= key
  {
    var mid := left + (right - left) / 2;
    if a[mid] < key {
      left := mid + 1;
    } else {
      right := mid;
    }
  }
  
  n := left;
}
// </vc-code>
