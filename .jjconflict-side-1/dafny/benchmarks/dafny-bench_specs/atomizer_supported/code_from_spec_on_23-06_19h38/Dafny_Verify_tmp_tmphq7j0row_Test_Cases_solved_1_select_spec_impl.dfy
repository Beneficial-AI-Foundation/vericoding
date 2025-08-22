//IMPL SelectionSort
method SelectionSort(a: array<int>)
  modifies a
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var n := a.Length;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant forall p,q :: 0 <= p < q < i ==> a[p] <= a[q]
    invariant forall p,q :: 0 <= p < i <= q < n ==> a[p] <= a[q]
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    var minIndex := i;
    var j := i + 1;
    
    while j < n
      invariant i <= minIndex < n
      invariant i + 1 <= j <= n
      invariant forall k :: i <= k < j ==> a[minIndex] <= a[k]
      invariant multiset(a[..]) == old(multiset(a[..]))
    {
      if a[j] < a[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    
    if minIndex != i {
      var temp := a[i];
      a[i] := a[minIndex];
      a[minIndex] := temp;
    }
    
    i := i + 1;
  }
}