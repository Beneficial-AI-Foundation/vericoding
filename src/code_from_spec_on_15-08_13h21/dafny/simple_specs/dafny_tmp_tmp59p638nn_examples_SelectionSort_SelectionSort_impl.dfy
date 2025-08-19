//ATOM
predicate Sorted(a: array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

//IMPL 
method SelectionSort(a: array<int>)
  modifies a
  ensures Sorted(a)
{
  var n := a.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k, l :: 0 <= k < i && i <= l < n ==> a[k] <= a[l]
    invariant forall k, l :: 0 <= k < l < i ==> a[k] <= a[l]
  {
    var minIndex := i;
    var j := i + 1;
    while j < n
      invariant i < j <= n
      invariant i <= minIndex < j
      invariant forall k :: i <= k < j ==> a[minIndex] <= a[k]
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