predicate Sorted(a: array<int>)
  reads a
{
  forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

method FindMin(a: array<int>, start: int) returns (minIndex: int)
  requires 0 <= start < a.Length
  ensures start <= minIndex < a.Length
  ensures forall k :: start <= k < a.Length ==> a[minIndex] <= a[k]
{
  minIndex := start;
  var i := start + 1;
  while i < a.Length
    invariant start <= minIndex < a.Length
    invariant start + 1 <= i <= a.Length
    invariant forall k :: start <= k < i ==> a[minIndex] <= a[k]
  {
    if a[i] < a[minIndex] {
      minIndex := i;
    }
    i := i + 1;
  }
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
    invariant forall p, q :: 0 <= p < q < i ==> a[p] <= a[q]
    invariant forall p, q :: 0 <= p < i && i <= q < n ==> a[p] <= a[q]
  {
    var minIndex := FindMin(a, i);
    
    // Swap a[i] and a[minIndex]
    var temp := a[i];
    a[i] := a[minIndex];
    a[minIndex] := temp;
    
    i := i + 1;
  }
}