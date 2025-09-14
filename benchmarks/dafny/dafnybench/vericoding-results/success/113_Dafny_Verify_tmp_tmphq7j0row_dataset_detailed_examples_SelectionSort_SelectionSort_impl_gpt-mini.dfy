// Works by dividing the input list into two parts: sorted and unsorted. At the beginning, 
// the sorted part is empty and the unsorted part contains all the elements.

// <vc-helpers>
method swap(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  modifies a
  ensures a[i] == old(a[j]) && a[j] == old(a[i])
  ensures (forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k]))
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var tmp := a[i];
  a[i] := a[j];
  a[j] := tmp;
}
// </vc-helpers>

// <vc-spec>
method SelectionSort(a: array<int>)
  modifies a
  // Ensures the final array is sorted in ascending order
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  // Ensures that the final array has the same elements as the initial array
  ensures multiset(a[..]) == old(multiset(a[..]))
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k,l :: 0 <= k < l < i ==> a[k] <= a[l]
    invariant forall k :: 0 <= k < i ==> forall t :: i <= t < n ==> a[k] <= a[t]
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    var minIdx := i;
    var j := i + 1;
    while j < n
      invariant i + 1 <= j <= n
      invariant i <= minIdx < n
      invariant forall t :: i <= t < j ==> a[minIdx] <= a[t]
      invariant forall k,l :: 0 <= k < l < i ==> a[k] <= a[l]
      invariant forall k :: 0 <= k < i ==> forall t :: i <= t < n ==> a[k] <= a[t]
      invariant multiset(a[..]) == old(multiset(a[..]))
    {
      if a[j] < a[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    swap(a, i, minIdx);
    i := i + 1;
  }
}
// </vc-code>

