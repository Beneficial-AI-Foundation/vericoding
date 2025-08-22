//IMPL 
method BinarySearch(a: array<int>, key: int) returns (n: int)
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures 0 <= n <= a.Length
  ensures forall i :: 0 <= i < n ==> a[i] < key
  ensures forall i :: n <= i < a.Length ==> key <= a[i]
{
  var low := 0;
  var high := a.Length;
  
  while low < high
    invariant 0 <= low <= high <= a.Length
    invariant forall i :: 0 <= i < low ==> a[i] < key
    invariant forall i :: high <= i < a.Length ==> key <= a[i]
  {
    var mid := (low + high) / 2;
    if a[mid] < key {
      low := mid + 1;
    } else {
      high := mid;
    }
  }
  
  n := low;
}