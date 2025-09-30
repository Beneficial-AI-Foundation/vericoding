

// <vc-helpers>
predicate IsSorted(a: array<int>, from: int, to: int)
  reads a
  requires 0 <= from <= to <= a.Length
{
  forall i, j :: from <= i < j < to ==> a[i] <= a[j]
}

predicate IsMinIndex(a: array<int>, from: int, to: int, minIndex: int)
  reads a
  requires 0 <= from <= to <= a.Length
  requires from <= minIndex < to
{
  forall k :: from <= k < to ==> a[minIndex] <= a[k]
}

lemma SwapMultisetPreservation(a: array<int>, i: int, j: int)
  requires 0 <= i < a.Length && 0 <= j < a.Length
  ensures multiset(a[..][i := a[j]][j := a[i]]) == multiset(a[..])
{
  var a' := a[..][i := a[j]][j := a[i]];
  assert a'[i] == a[j] && a'[j] == a[i];
  assert forall k :: 0 <= k < a.Length && k != i && k != j ==> a'[k] == a[k];
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
    invariant IsSorted(a, 0, i)
    invariant forall x, y :: 0 <= x < i <= y < a.Length ==> a[x] <= a[y]
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    var minIndex := i;
    var j := i + 1;
    
    while j < a.Length
      invariant i < j <= a.Length
      invariant i <= minIndex < j
      invariant IsMinIndex(a, i, j, minIndex)
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
      SwapMultisetPreservation(a, i, minIndex);
    }
    
    i := i + 1;
  }
}
// </vc-code>

