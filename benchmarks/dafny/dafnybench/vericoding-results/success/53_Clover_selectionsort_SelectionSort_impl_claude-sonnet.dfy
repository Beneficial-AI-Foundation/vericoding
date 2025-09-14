

// <vc-helpers>
lemma MultisetPreservation(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length && 0 <= j < a.Length
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

lemma SortedPrefix(a: array<int>, k: int)
  requires 0 <= k <= a.Length
  requires forall i,j :: 0 <= i < j < k ==> a[i] <= a[j]
  requires forall i,j :: 0 <= i < k && k <= j < a.Length ==> a[i] <= a[j]
  ensures forall i,j :: 0 <= i < j < a.Length && j < k ==> a[i] <= a[j]
{}
// </vc-helpers>

// <vc-spec>
method SelectionSort(a: array<int>)
  modifies a
  ensures forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == old(multiset(a[..]))
// </vc-spec>
// <vc-code>
{
  var n := a.Length;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant forall x,y :: 0 <= x < y < i ==> a[x] <= a[y]
    invariant forall x,y :: 0 <= x < i && i <= y < n ==> a[x] <= a[y]
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    var minIndex := i;
    var j := i + 1;
    
    while j < n
      invariant i <= minIndex < n
      invariant i <= j <= n
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
      var temp := a[i];
      a[i] := a[minIndex];
      a[minIndex] := temp;
    }
    
    i := i + 1;
  }
}
// </vc-code>

