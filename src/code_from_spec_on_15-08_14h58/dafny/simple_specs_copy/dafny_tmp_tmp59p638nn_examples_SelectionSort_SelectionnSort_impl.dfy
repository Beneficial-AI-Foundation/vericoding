predicate Sorted(a: array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

//IMPL
method SelectionnSort(a: array<int>)
  modifies a
  ensures Sorted(a)
{
  var n := a.Length;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant forall x, y :: 0 <= x < y < i ==> a[x] <= a[y]
    invariant forall x, y :: 0 <= x < i <= y < n ==> a[x] <= a[y]
  {
    var minIndex := i;
    var j := i + 1;
    
    while j < n
      invariant i <= minIndex < n
      invariant i + 1 <= j <= n
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