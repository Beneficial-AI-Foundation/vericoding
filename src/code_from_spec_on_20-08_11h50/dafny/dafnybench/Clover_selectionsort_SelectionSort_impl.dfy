lemma MultisetPreservation(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  ensures multiset(a[..][i := a[j]][j := a[i]]) == multiset(a[..])
{
  var original := a[..];
  var swapped := original[i := a[j]][j := a[i]];
  
  if i == j {
    assert swapped == original;
  } else {
    assert multiset(swapped) == multiset(original);
  }
}
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
    invariant forall x,y :: 0 <= x < y < i ==> a[x] <= a[y]
    invariant forall x,y :: 0 <= x < i <= y < a.Length ==> a[x] <= a[y]
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    var minIndex := i;
    var j := i + 1;
    
    while j < a.Length
      invariant i <= minIndex < a.Length
      invariant i <= j <= a.Length
      invariant forall k :: i <= k < j ==> a[minIndex] <= a[k]
      invariant multiset(a[..]) == old(multiset(a[..]))
    {
      if a[j] < a[minIndex] {
        minIndex := j;
      }
      j := j + 1;
    }
    
    if minIndex != i {
      MultisetPreservation(a, i, minIndex);
      a[i], a[minIndex] := a[minIndex], a[i];
    }
    
    i := i + 1;
  }
}
// </vc-code>