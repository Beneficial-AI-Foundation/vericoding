//https://homepage.cs.uiowa.edu/~tinelli/classes/181/Fall21/Tools/Dafny/Examples/selection-sort.shtml



predicate sorted (a: array<int>)
    requires a != null
    reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}


// Selection sort on arrays

// <vc-helpers>
lemma SortedExtension(a: array<int>, k: int)
  requires a != null
  requires 0 <= k < a.Length
  requires forall i, j :: 0 <= i < j < k ==> a[i] <= a[j]
  requires forall i :: 0 <= i < k ==> forall j :: k <= j < a.Length ==> a[i] <= a[j]
  requires forall i, j :: k <= i < j < a.Length ==> a[i] <= a[j]
  ensures sorted(a)
{
  // The lemma body is empty because Dafny can prove this automatically
  // from the three premises about the sorted prefix, the relationship
  // between prefix and suffix, and the sorted suffix
}
// </vc-helpers>

// <vc-spec>
method SelectionSort(a: array<int>) 
  modifies a
  ensures sorted(a)
  //ensures multiset(old(a[..])) == multiset(a[..])
// </vc-spec>
// <vc-code>
{
  if a.Length <= 1 {
    return;
  }
  
  var i := 0;
  while i < a.Length - 1
    invariant 0 <= i <= a.Length - 1
    invariant forall p, q :: 0 <= p < q < i ==> a[p] <= a[q]
    invariant forall p :: 0 <= p < i ==> forall q :: i <= q < a.Length ==> a[p] <= a[q]
  {
    var minIndex := i;
    var j := i + 1;
    
    while j < a.Length
      invariant i < j <= a.Length
      invariant i <= minIndex < j
      invariant forall k :: i <= k < j ==> a[minIndex] <= a[k]
    {
      if a[j] < a[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    
    // Swap a[i] and a[minIndex]
    var temp := a[i];
    a[i] := a[minIndex];
    a[minIndex] := temp;
    
    i := i + 1;
  }
  
  // Apply the helper lemma to conclude that the array is sorted
  SortedExtension(a, a.Length - 1);
}
// </vc-code>