class Benchmark2 {

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method BinarySearch(a: array<int>, key: int) returns (result: int)
    requires forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j];
    ensures -1 <= result < a.Length;
    ensures 0 <= result ==> a[result] == key;
    ensures result == -1 ==> forall i :: 0 <= i < a.Length ==> a[i] != key;
// </vc-spec>
// <vc-code>
{
  var low := 0;
  var high := a.Length;
  
  while low < high
    invariant 0 <= low <= high <= a.Length;
    invariant forall i :: 0 <= i < low ==> a[i] < key;
    invariant forall i :: high <= i < a.Length ==> a[i] > key;
  {
    var mid := (low + high) / 2;
    
    if a[mid] < key {
      low := mid + 1;
    } else if a[mid] > key {
      high := mid;
    } else {
      return mid;
    }
  }
  
  return -1;
}
// </vc-code>

}