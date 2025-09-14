

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method SelectionSort(a: array<int>)
  modifies a
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant multiset(a[..]) == old(multiset(a[..]))
    invariant forall k, m :: 0 <= k < m < i ==> a[k] <= a[m]
    invariant forall k, m :: 0 <= k < i <= m < a.Length ==> a[k] <= a[m]
  {
    var minIdx := i;
    var j := i + 1;
    while j < a.Length
      invariant i <= minIdx < j <= a.Length
      invariant forall p :: i <= p < j ==> a[minIdx] <= a[p]
    {
      if a[j] < a[minIdx] {
        minIdx := j;
      }
      j := j + 1;
    }
    var temp := a[i];
    a[i] := a[minIdx];
    a[minIdx] := temp;
    i := i + 1;
  }
}
// </vc-code>

