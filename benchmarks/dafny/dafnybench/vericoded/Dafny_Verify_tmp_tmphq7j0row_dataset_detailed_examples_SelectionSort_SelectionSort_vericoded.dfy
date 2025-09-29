// Works by dividing the input list into two parts: sorted and unsorted. At the beginning, 
// the sorted part is empty and the unsorted part contains all the elements.

// <vc-helpers>
// Predicate to check if a portion of the array is sorted
predicate Sorted(a: array<int>, from: int, to: int)
  reads a
  requires 0 <= from <= to <= a.Length
{
  forall i, j :: from <= i < j < to ==> a[i] <= a[j]
}

// Predicate to check partition property: all elements in sorted part are <= all elements in unsorted part
predicate Partitioned(a: array<int>, index: int)
  reads a
  requires 0 <= index <= a.Length
{
  forall i, j :: 0 <= i < index <= j < a.Length ==> a[i] <= a[j]
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
    invariant Sorted(a, 0, i)
    invariant Partitioned(a, i)
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    // Find the minimum element in the unsorted portion
    var minIndex := i;
    var j := i + 1;
    
    while j < n
      invariant i < j <= n
      invariant i <= minIndex < n
      invariant forall k :: i <= k < j ==> a[minIndex] <= a[k]
    {
      if a[j] < a[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    
    // Swap the minimum element with a[i]
    if minIndex != i {
      var temp := a[i];
      a[i] := a[minIndex];
      a[minIndex] := temp;
    }
    
    i := i + 1;
  }
}
// </vc-code>

