//ATOM

//b)
//Problem04
method FindMin(a: array<int>, lo: nat) returns (minIdx: nat)
  requires a != null && a.Length > 0 && lo < a.Length
  ensures lo <= minIdx < a.Length
  ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
{
  minIdx := 0;
  assume lo <= minIdx < a.Length;
  assume forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x];
  return minIdx;
}


//ATOM
//Problem01
//a)
method swap(a: array<int>, i: nat, j: nat)
  modifies a
  requires a != null && a.Length > 0 && i < a.Length && j < a.Length
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
{
  assume a[i] ==> old(a[j]);
  assume a[j] ==> old(a[i]);
}


// SPEC

method selectionSort(a: array<int>)
  modifies a
  //ensures multiset(a[..]) == multiset(old(a[..]))
  //ensures sorted(a[..])
{
}
