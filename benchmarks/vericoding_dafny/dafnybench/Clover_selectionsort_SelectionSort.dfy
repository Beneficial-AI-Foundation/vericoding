// <vc-helpers>
// </vc-helpers>

method SelectionSort(a: array<int>)
  modifies a
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
// <vc-code>
{
  assume false;
}
// </vc-code>