method SelectionSort(a: array<int>)
  modifies a
  // Ensures the final array is sorted in ascending order
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  // Ensures that the final array has the same elements as the initial array
  ensures multiset(a[..]) == old(multiset(a[..]))
// </vc-spec>
// <vc-code>
{
  if a.Length <= 1 { return; }
  
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    // The sorted part (0..i) is sorted
    invariant forall x, y :: 0 <= x < y < i ==> a[x] <= a[y]
    // Elements in sorted part are <= elements in unsorted part
    invariant forall x, y :: 0 <= x < i <= y < a.Length ==> a[x] <= a[y]
    // Multiset is preserved
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    // Find minimum element in unsorted part
    var minIndex := i;
    var j := i + 1;
    
    while j < a.Length
      invariant i <= minIndex < a.Length
      invariant i + 1 <= j <= a.Length
      invariant forall k :: i <= k < j ==> a[minIndex] <= a[k]
    {
      if a[j] < a[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    
    // Swap minimum element with first element of unsorted part
    if minIndex != i {
      var temp := a[i];
      a[i] := a[minIndex];
      a[minIndex] := temp;
    }
    
    i := i + 1;
  }
}
// </vc-code>